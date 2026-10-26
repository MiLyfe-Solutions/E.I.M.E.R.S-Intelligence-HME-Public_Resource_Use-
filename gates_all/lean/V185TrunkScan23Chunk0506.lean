import V185TrunkScan23Chunk0505

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2993576 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2993576 : Nat := 118140960795 + 2993576 * 2 ^ 59
def prefixEnd_2993576 : Nat := 4983230072969 + 3 ^ 40 * 2993576 * 2
def baseEnd_2993576 : Nat := 1537143363763884853832801

theorem tailTrace_2993576 : CollatzResearch.WordTrace tailWord_2993576 prefixEnd_2993576 1537143363763884853832801 := by
  unfold tailWord_2993576
  simp only [CollatzResearch.WordTrace]
  refine ⟨54592343301396444461128291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72789791068528592614837721 54592343301396444461128291)
  ·
    refine ⟨81888514952094666691692437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54592343301396444461128291 81888514952094666691692437)
    ·
      refine ⟨3838524138379437501173083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81888514952094666691692437 3838524138379437501173083)
      ·
        refine ⟨5757786207569156251759625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838524138379437501173083 5757786207569156251759625)
        ·
          refine ⟨4318339655676867188819719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757786207569156251759625 4318339655676867188819719)
          ·
            refine ⟨6477509483515300783229579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318339655676867188819719 6477509483515300783229579)
            ·
              refine ⟨9716264225272951174844369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477509483515300783229579 9716264225272951174844369)
              ·
                refine ⟨7287198168954713381133277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9716264225272951174844369 7287198168954713381133277)
                ·
                  refine ⟨2732699313358017517924979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7287198168954713381133277 2732699313358017517924979)
                  ·
                    refine ⟨4099048970037026276887469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2732699313358017517924979 4099048970037026276887469)
                    ·
                      refine ⟨1537143363763884853832801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099048970037026276887469 1537143363763884853832801)
                      ·
                        rfl

theorem cell23_2993576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2993576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993576 prefixEnd_2993576 := by exact prefixLift 2993576
  have htrace : WordTrace (prefixWord ++ tailWord_2993576) baseStart_2993576 baseEnd_2993576 := by
    simpa [prefixWord, tailWord_2993576, baseEnd_2993576] using wordTrace_append hprefix tailTrace_2993576
  have hstable : (prefixWord ++ tailWord_2993576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993576).length < 2 ^ (prefixWord ++ tailWord_2993576).sum := by decide
  have hdescent : baseEnd_2993576 < baseStart_2993576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993596 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_2993596 : Nat := 118140960795 + 2993596 * 2 ^ 59
def prefixEnd_2993596 : Nat := 4983230072969 + 3 ^ 40 * 2993596 * 2
def baseEnd_2993596 : Nat := 512384544458991591860903

theorem tailTrace_2993596 : CollatzResearch.WordTrace tailWord_2993596 prefixEnd_2993596 512384544458991591860903 := by
  unfold tailWord_2993596
  simp only [CollatzResearch.WordTrace]
  refine ⟨54592708031360216168992321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72790277375146954891989761 54592708031360216168992321)
  ·
    refine ⟨40944531023520162126744241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54592708031360216168992321 40944531023520162126744241)
    ·
      refine ⟨30708398267640121595058181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40944531023520162126744241 30708398267640121595058181)
      ·
        refine ⟨5757824675182522799073409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30708398267640121595058181 5757824675182522799073409)
        ·
          refine ⟨4318368506386892099305057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757824675182522799073409 4318368506386892099305057)
          ·
            refine ⟨3238776379790169074478793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318368506386892099305057 3238776379790169074478793)
            ·
              refine ⟨2429082284842626805859095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3238776379790169074478793 2429082284842626805859095)
              ·
                refine ⟨3643623427263940208788643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429082284842626805859095 3643623427263940208788643)
                ·
                  refine ⟨5465435140895910313182965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643623427263940208788643 5465435140895910313182965)
                  ·
                    refine ⟨512384544458991591860903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5465435140895910313182965 512384544458991591860903)
                    ·
                      rfl

theorem cell23_2993596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_2993596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993596 prefixEnd_2993596 := by exact prefixLift 2993596
  have htrace : WordTrace (prefixWord ++ tailWord_2993596) baseStart_2993596 baseEnd_2993596 := by
    simpa [prefixWord, tailWord_2993596, baseEnd_2993596] using wordTrace_append hprefix tailTrace_2993596
  have hstable : (prefixWord ++ tailWord_2993596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993596).length < 2 ^ (prefixWord ++ tailWord_2993596).sum := by decide
  have hdescent : baseEnd_2993596 < baseStart_2993596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993615 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_2993615 : Nat := 118140960795 + 2993615 * 2 ^ 59
def prefixEnd_2993615 : Nat := 4983230072969 + 3 ^ 40 * 2993615 * 2
def baseEnd_2993615 : Nat := 1537163389509410201245121

theorem tailTrace_2993615 : CollatzResearch.WordTrace tailWord_2993615 prefixEnd_2993615 1537163389509410201245121 := by
  unfold tailWord_2993615
  simp only [CollatzResearch.WordTrace]
  refine ⟨109186109049651598582926299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72790739366434399055284199 109186109049651598582926299)
  ·
    refine ⟨163779163574477397874389449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109186109049651598582926299 163779163574477397874389449)
    ·
      refine ⟨122834372680858048405792087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163779163574477397874389449 122834372680858048405792087)
      ·
        refine ⟨184251559021287072608688131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122834372680858048405792087 184251559021287072608688131)
        ·
          refine ⟨276377338531930608913032197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184251559021287072608688131 276377338531930608913032197)
          ·
            refine ⟨51820750974736989171193537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276377338531930608913032197 51820750974736989171193537)
            ·
              refine ⟨38865563231052741878395153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51820750974736989171193537 38865563231052741878395153)
              ·
                refine ⟨29149172423289556408796365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38865563231052741878395153 29149172423289556408796365)
                ·
                  refine ⟨10930939658733583653298637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29149172423289556408796365 10930939658733583653298637)
                  ·
                    refine ⟨4099102372025093869986989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10930939658733583653298637 4099102372025093869986989)
                    ·
                      refine ⟨1537163389509410201245121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099102372025093869986989 1537163389509410201245121)
                      ·
                        rfl

theorem cell23_2993615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_2993615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993615 prefixEnd_2993615 := by exact prefixLift 2993615
  have htrace : WordTrace (prefixWord ++ tailWord_2993615) baseStart_2993615 baseEnd_2993615 := by
    simpa [prefixWord, tailWord_2993615, baseEnd_2993615] using wordTrace_append hprefix tailTrace_2993615
  have hstable : (prefixWord ++ tailWord_2993615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993615).length < 2 ^ (prefixWord ++ tailWord_2993615).sum := by decide
  have hdescent : baseEnd_2993615 < baseStart_2993615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993629 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2993629 : Nat := 118140960795 + 2993629 * 2 ^ 59
def prefixEnd_2993629 : Nat := 4983230072969 + 3 ^ 40 * 2993629 * 2
def baseEnd_2993629 : Nat := 1537170578238573146470057

theorem tailTrace_2993629 : CollatzResearch.WordTrace tailWord_2993629 prefixEnd_2993629 1537170578238573146470057 := by
  unfold tailWord_2993629
  simp only [CollatzResearch.WordTrace]
  refine ⟨109186619671600878973935941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72791079781067252649290627 109186619671600878973935941)
  ·
    refine ⟨20472491188425164807612989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109186619671600878973935941 20472491188425164807612989)
    ·
      refine ⟨7677184195659436802854871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20472491188425164807612989 7677184195659436802854871)
      ·
        refine ⟨11515776293489155204282307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7677184195659436802854871 11515776293489155204282307)
        ·
          refine ⟨17273664440233732806423461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11515776293489155204282307 17273664440233732806423461)
          ·
            refine ⟨3238812082543824901204399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17273664440233732806423461 3238812082543824901204399)
            ·
              refine ⟨4858218123815737351806599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238812082543824901204399 4858218123815737351806599)
              ·
                refine ⟨7287327185723606027709899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4858218123815737351806599 7287327185723606027709899)
                ·
                  refine ⟨10930990778585409041564849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7287327185723606027709899 10930990778585409041564849)
                  ·
                    refine ⟨8198243083939056781173637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10930990778585409041564849 8198243083939056781173637)
                    ·
                      refine ⟨1537170578238573146470057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8198243083939056781173637 1537170578238573146470057)
                      ·
                        rfl

theorem cell23_2993629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2993629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993629 prefixEnd_2993629 := by exact prefixLift 2993629
  have htrace : WordTrace (prefixWord ++ tailWord_2993629) baseStart_2993629 baseEnd_2993629 := by
    simpa [prefixWord, tailWord_2993629, baseEnd_2993629] using wordTrace_append hprefix tailTrace_2993629
  have hstable : (prefixWord ++ tailWord_2993629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993629).length < 2 ^ (prefixWord ++ tailWord_2993629).sum := by decide
  have hdescent : baseEnd_2993629 < baseStart_2993629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993650 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_2993650 : Nat := 118140960795 + 2993650 * 2 ^ 59
def prefixEnd_2993650 : Nat := 4983230072969 + 3 ^ 40 * 2993650 * 2
def baseEnd_2993650 : Nat := 1537181361332317564307461

theorem tailTrace_2993650 : CollatzResearch.WordTrace tailWord_2993650 prefixEnd_2993650 1537181361332317564307461 := by
  unfold tailWord_2993650
  simp only [CollatzResearch.WordTrace]
  refine ⟨27296846401131199890112601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72791590403016533040300269 27296846401131199890112601)
  ·
    refine ⟨20472634800848399917584451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27296846401131199890112601 20472634800848399917584451)
    ·
      refine ⟨30708952201272599876376677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20472634800848399917584451 30708952201272599876376677)
      ·
        refine ⟨5757928537738612476820627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30708952201272599876376677 5757928537738612476820627)
        ·
          refine ⟨8636892806607918715230941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757928537738612476820627 8636892806607918715230941)
          ·
            refine ⟨3238834802477969518211603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8636892806607918715230941 3238834802477969518211603)
            ·
              refine ⟨4858252203716954277317405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238834802477969518211603 4858252203716954277317405)
              ·
                refine ⟨1821844576393857853994027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4858252203716954277317405 1821844576393857853994027)
                ·
                  refine ⟨2732766864590786780991041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821844576393857853994027 2732766864590786780991041)
                  ·
                    refine ⟨2049575148443090085743281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2732766864590786780991041 2049575148443090085743281)
                    ·
                      refine ⟨1537181361332317564307461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049575148443090085743281 1537181361332317564307461)
                      ·
                        rfl

theorem cell23_2993650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_2993650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993650 prefixEnd_2993650 := by exact prefixLift 2993650
  have htrace : WordTrace (prefixWord ++ tailWord_2993650) baseStart_2993650 baseEnd_2993650 := by
    simpa [prefixWord, tailWord_2993650, baseEnd_2993650] using wordTrace_append hprefix tailTrace_2993650
  have hstable : (prefixWord ++ tailWord_2993650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993650).length < 2 ^ (prefixWord ++ tailWord_2993650).sum := by decide
  have hdescent : baseEnd_2993650 < baseStart_2993650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993666 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2993666 : Nat := 118140960795 + 2993666 * 2 ^ 59
def prefixEnd_2993666 : Nat := 4983230072969 + 3 ^ 40 * 2993666 * 2
def baseEnd_2993666 : Nat := 1537189577022789501707387

theorem tailTrace_2993666 : CollatzResearch.WordTrace tailWord_2993666 prefixEnd_2993666 1537189577022789501707387 := by
  unfold tailWord_2993666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27296992293116708573258213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72791979448311222862021901 27296992293116708573258213)
  ·
    refine ⟨5118186054959382857485915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27296992293116708573258213 5118186054959382857485915)
    ·
      refine ⟨7677279082439074286228873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118186054959382857485915 7677279082439074286228873)
      ·
        refine ⟨5757959311829305714671655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7677279082439074286228873 5757959311829305714671655)
        ·
          refine ⟨8636938967743958572007483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757959311829305714671655 8636938967743958572007483)
          ·
            refine ⟨12955408451615937858011225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8636938967743958572007483 12955408451615937858011225)
            ·
              refine ⟨9716556338711953393508419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12955408451615937858011225 9716556338711953393508419)
              ·
                refine ⟨14574834508067930090262629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9716556338711953393508419 14574834508067930090262629)
                ·
                  refine ⟨2732781470262736891924243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14574834508067930090262629 2732781470262736891924243)
                  ·
                    refine ⟨4099172205394105337886365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2732781470262736891924243 4099172205394105337886365)
                    ·
                      refine ⟨1537189577022789501707387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099172205394105337886365 1537189577022789501707387)
                      ·
                        rfl

theorem cell23_2993666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2993666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993666 prefixEnd_2993666 := by exact prefixLift 2993666
  have htrace : WordTrace (prefixWord ++ tailWord_2993666) baseStart_2993666 baseEnd_2993666 := by
    simpa [prefixWord, tailWord_2993666, baseEnd_2993666] using wordTrace_append hprefix tailTrace_2993666
  have hstable : (prefixWord ++ tailWord_2993666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993666).length < 2 ^ (prefixWord ++ tailWord_2993666).sum := by decide
  have hdescent : baseEnd_2993666 < baseStart_2993666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993677 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2993677 : Nat := 118140960795 + 2993677 * 2 ^ 59
def prefixEnd_2993677 : Nat := 4983230072969 + 3 ^ 40 * 2993677 * 2
def baseEnd_2993677 : Nat := 512398408436662986223279

theorem tailTrace_2993677 : CollatzResearch.WordTrace tailWord_2993677 prefixEnd_2993677 512398408436662986223279 := by
  unfold tailWord_2993677
  simp only [CollatzResearch.WordTrace]
  refine ⟨109188370375426983171683285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72792246916951322114455523 109188370375426983171683285)
  ·
    refine ⟨2559102430674069918086327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 109188370375426983171683285 2559102430674069918086327)
    ·
      refine ⟨3838653646011104877129491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559102430674069918086327 3838653646011104877129491)
      ·
        refine ⟨5757980469016657315694237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838653646011104877129491 5757980469016657315694237)
        ·
          refine ⟨2159242675881246493385339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5757980469016657315694237 2159242675881246493385339)
          ·
            refine ⟨3238864013821869740078009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159242675881246493385339 3238864013821869740078009)
            ·
              refine ⟨2429148010366402305058507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3238864013821869740078009 2429148010366402305058507)
              ·
                refine ⟨3643722015549603457587761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429148010366402305058507 3643722015549603457587761)
                ·
                  refine ⟨2732791511662202593190821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643722015549603457587761 2732791511662202593190821)
                  ·
                    refine ⟨512398408436662986223279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2732791511662202593190821 512398408436662986223279)
                    ·
                      rfl

theorem cell23_2993677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2993677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993677 prefixEnd_2993677 := by exact prefixLift 2993677
  have htrace : WordTrace (prefixWord ++ tailWord_2993677) baseStart_2993677 baseEnd_2993677 := by
    simpa [prefixWord, tailWord_2993677, baseEnd_2993677] using wordTrace_append hprefix tailTrace_2993677
  have hstable : (prefixWord ++ tailWord_2993677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993677).length < 2 ^ (prefixWord ++ tailWord_2993677).sum := by decide
  have hdescent : baseEnd_2993677 < baseStart_2993677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993695 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 7]
def baseStart_2993695 : Nat := 118140960795 + 2993695 * 2 ^ 59
def prefixEnd_2993695 : Nat := 4983230072969 + 3 ^ 40 * 2993695 * 2
def baseEnd_2993695 : Nat := 170800496440196654249417

theorem tailTrace_2993695 : CollatzResearch.WordTrace tailWord_2993695 prefixEnd_2993695 170800496440196654249417 := by
  unfold tailWord_2993695
  simp only [CollatzResearch.WordTrace]
  refine ⟨109189026889361772245838539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72792684592907848163892359 109189026889361772245838539)
  ·
    refine ⟨163783540334042658368757809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109189026889361772245838539 163783540334042658368757809)
    ·
      refine ⟨122837655250531993776568357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163783540334042658368757809 122837655250531993776568357)
      ·
        refine ⟨23032060359474748833106567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122837655250531993776568357 23032060359474748833106567)
        ·
          refine ⟨34548090539212123249659851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23032060359474748833106567 34548090539212123249659851)
          ·
            refine ⟨51822135808818184874489777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34548090539212123249659851 51822135808818184874489777)
            ·
              refine ⟨38866601856613638655867333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51822135808818184874489777 38866601856613638655867333)
              ·
                refine ⟨7287487848115057247975125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38866601856613638655867333 7287487848115057247975125)
                ·
                  refine ⟨170800496440196654249417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7287487848115057247975125 170800496440196654249417)
                  ·
                    rfl

theorem cell23_2993695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 7].length) (baseStart_2993695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993695 prefixEnd_2993695 := by exact prefixLift 2993695
  have htrace : WordTrace (prefixWord ++ tailWord_2993695) baseStart_2993695 baseEnd_2993695 := by
    simpa [prefixWord, tailWord_2993695, baseEnd_2993695] using wordTrace_append hprefix tailTrace_2993695
  have hstable : (prefixWord ++ tailWord_2993695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993695).length < 2 ^ (prefixWord ++ tailWord_2993695).sum := by decide
  have hdescent : baseEnd_2993695 < baseStart_2993695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993712 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 5]
def baseStart_2993712 : Nat := 118140960795 + 2993712 * 2 ^ 59
def prefixEnd_2993712 : Nat := 4983230072969 + 3 ^ 40 * 2993712 * 2
def baseEnd_2993712 : Nat := 170801466348099591303575

theorem tailTrace_2993712 : CollatzResearch.WordTrace tailWord_2993712 prefixEnd_2993712 170801466348099591303575 := by
  unfold tailWord_2993712
  simp only [CollatzResearch.WordTrace]
  refine ⟨54594823465150092074603695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72793097953533456099471593 54594823465150092074603695)
  ·
    refine ⟨81892235197725138111905543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54594823465150092074603695 81892235197725138111905543)
    ·
      refine ⟨122838352796587707167858315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81892235197725138111905543 122838352796587707167858315)
      ·
        refine ⟨184257529194881560751787473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122838352796587707167858315 184257529194881560751787473)
        ·
          refine ⟨138193146896161170563840605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184257529194881560751787473 138193146896161170563840605)
          ·
            refine ⟨51822430086060438961440227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138193146896161170563840605 51822430086060438961440227)
            ·
              refine ⟨77733645129090658442160341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51822430086060438961440227 77733645129090658442160341)
              ·
                refine ⟨1821882307713062307238133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77733645129090658442160341 1821882307713062307238133)
                ·
                  refine ⟨170801466348099591303575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821882307713062307238133 170801466348099591303575)
                  ·
                    rfl

theorem cell23_2993712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 5].length) (baseStart_2993712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993712 prefixEnd_2993712 := by exact prefixLift 2993712
  have htrace : WordTrace (prefixWord ++ tailWord_2993712) baseStart_2993712 baseEnd_2993712 := by
    simpa [prefixWord, tailWord_2993712, baseEnd_2993712] using wordTrace_append hprefix tailTrace_2993712
  have hstable : (prefixWord ++ tailWord_2993712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993712).length < 2 ^ (prefixWord ++ tailWord_2993712).sum := by decide
  have hdescent : baseEnd_2993712 < baseStart_2993712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993722 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_2993722 : Nat := 118140960795 + 2993722 * 2 ^ 59
def prefixEnd_2993722 : Nat := 4983230072969 + 3 ^ 40 * 2993722 * 2
def baseEnd_2993722 : Nat := 1537218331939441282607129

theorem tailTrace_2993722 : CollatzResearch.WordTrace tailWord_2993722 prefixEnd_2993722 1537218331939441282607129 := by
  unfold tailWord_2993722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27297502915065988964267855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72793341106842637238047613 27297502915065988964267855)
  ·
    refine ⟨40946254372598983446401783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27297502915065988964267855 40946254372598983446401783)
    ·
      refine ⟨61419381558898475169602675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40946254372598983446401783 61419381558898475169602675)
      ·
        refine ⟨92129072338347712754404013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61419381558898475169602675 92129072338347712754404013)
        ·
          refine ⟨34548402126880392282901505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92129072338347712754404013 34548402126880392282901505)
          ·
            refine ⟨25911301595160294212176129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34548402126880392282901505 25911301595160294212176129)
            ·
              refine ⟨19433476196370220659132097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25911301595160294212176129 19433476196370220659132097)
              ·
                refine ⟨14575107147277665494349073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19433476196370220659132097 14575107147277665494349073)
                ·
                  refine ⟨10931330360458249120761805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14575107147277665494349073 10931330360458249120761805)
                  ·
                    refine ⟨4099248885171843420285677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10931330360458249120761805 4099248885171843420285677)
                    ·
                      refine ⟨1537218331939441282607129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099248885171843420285677 1537218331939441282607129)
                      ·
                        rfl

theorem cell23_2993722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_2993722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993722 prefixEnd_2993722 := by exact prefixLift 2993722
  have htrace : WordTrace (prefixWord ++ tailWord_2993722) baseStart_2993722 baseEnd_2993722 := by
    simpa [prefixWord, tailWord_2993722, baseEnd_2993722] using wordTrace_append hprefix tailTrace_2993722
  have hstable : (prefixWord ++ tailWord_2993722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993722).length < 2 ^ (prefixWord ++ tailWord_2993722).sum := by decide
  have hdescent : baseEnd_2993722 < baseStart_2993722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993729 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 5]
def baseStart_2993729 : Nat := 118140960795 + 2993729 * 2 ^ 59
def prefixEnd_2993729 : Nat := 4983230072969 + 3 ^ 40 * 2993729 * 2
def baseEnd_2993729 : Nat := 170802436256002528357733

theorem tailTrace_2993729 : CollatzResearch.WordTrace tailWord_2993729 prefixEnd_2993729 170802436256002528357733 := by
  unfold tailWord_2993729
  simp only [CollatzResearch.WordTrace]
  refine ⟨109190266971238596052576241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72793511314159064035050827 109190266971238596052576241)
  ·
    refine ⟨81892700228428947039432181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109190266971238596052576241 81892700228428947039432181)
    ·
      refine ⟨7677440646415213784946767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81892700228428947039432181 7677440646415213784946767)
      ·
        refine ⟨11516160969622820677420151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7677440646415213784946767 11516160969622820677420151)
        ·
          refine ⟨17274241454434231016130227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11516160969622820677420151 17274241454434231016130227)
          ·
            refine ⟨25911362181651346524195341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17274241454434231016130227 25911362181651346524195341)
            ·
              refine ⟨9716760818119254946573253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25911362181651346524195341 9716760818119254946573253)
              ·
                refine ⟨1821892653397360302482485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9716760818119254946573253 1821892653397360302482485)
                ·
                  refine ⟨170802436256002528357733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821892653397360302482485 170802436256002528357733)
                  ·
                    rfl

theorem cell23_2993729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 5].length) (baseStart_2993729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993729 prefixEnd_2993729 := by exact prefixLift 2993729
  have htrace : WordTrace (prefixWord ++ tailWord_2993729) baseStart_2993729 baseEnd_2993729 := by
    simpa [prefixWord, tailWord_2993729, baseEnd_2993729] using wordTrace_append hprefix tailTrace_2993729
  have hstable : (prefixWord ++ tailWord_2993729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993729).length < 2 ^ (prefixWord ++ tailWord_2993729).sum := by decide
  have hdescent : baseEnd_2993729 < baseStart_2993729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993772 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_2993772 : Nat := 118140960795 + 2993772 * 2 ^ 59
def prefixEnd_2993772 : Nat := 4983230072969 + 3 ^ 40 * 2993772 * 2
def baseEnd_2993772 : Nat := 512414668657388695660633

theorem tailTrace_2993772 : CollatzResearch.WordTrace tailWord_2993772 prefixEnd_2993772 512414668657388695660633 := by
  unfold tailWord_2993772
  simp only [CollatzResearch.WordTrace]
  refine ⟨54595917655041407198195785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72794556873388542930927713 54595917655041407198195785)
  ·
    refine ⟨40946938241281055398646839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54595917655041407198195785 40946938241281055398646839)
    ·
      refine ⟨61420407361921583097970259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40946938241281055398646839 61420407361921583097970259)
      ·
        refine ⟨92130611042882374646955389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61420407361921583097970259 92130611042882374646955389)
        ·
          refine ⟨34548979141080890492608271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92130611042882374646955389 34548979141080890492608271)
          ·
            refine ⟨51823468711621335738912407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34548979141080890492608271 51823468711621335738912407)
            ·
              refine ⟨77735203067432003608368611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51823468711621335738912407 77735203067432003608368611)
              ·
                refine ⟨116602804601148005412552917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77735203067432003608368611 116602804601148005412552917)
                ·
                  refine ⟨2732878232839406376856709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116602804601148005412552917 2732878232839406376856709)
                  ·
                    refine ⟨512414668657388695660633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2732878232839406376856709 512414668657388695660633)
                    ·
                      rfl

theorem cell23_2993772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_2993772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993772 prefixEnd_2993772 := by exact prefixLift 2993772
  have htrace : WordTrace (prefixWord ++ tailWord_2993772) baseStart_2993772 baseEnd_2993772 := by
    simpa [prefixWord, tailWord_2993772, baseEnd_2993772] using wordTrace_append hprefix tailTrace_2993772
  have hstable : (prefixWord ++ tailWord_2993772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993772).length < 2 ^ (prefixWord ++ tailWord_2993772).sum := by decide
  have hdescent : baseEnd_2993772 < baseStart_2993772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993789 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2993789 : Nat := 118140960795 + 2993789 * 2 ^ 59
def prefixEnd_2993789 : Nat := 4983230072969 + 3 ^ 40 * 2993789 * 2
def baseEnd_2993789 : Nat := 512417578381097506823107

theorem tailTrace_2993789 : CollatzResearch.WordTrace tailWord_2993789 prefixEnd_2993789 512417578381097506823107 := by
  unfold tailWord_2993789
  simp only [CollatzResearch.WordTrace]
  refine ⟨109192455351021226299760421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72794970234014150866506947 109192455351021226299760421)
  ·
    refine ⟨20473585378316479931205079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109192455351021226299760421 20473585378316479931205079)
    ·
      refine ⟨30710378067474719896807619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20473585378316479931205079 30710378067474719896807619)
      ·
        refine ⟨46065567101212079845211429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30710378067474719896807619 46065567101212079845211429)
        ·
          refine ⟨8637293831477264970977143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46065567101212079845211429 8637293831477264970977143)
          ·
            refine ⟨12955940747215897456465715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8637293831477264970977143 12955940747215897456465715)
            ·
              refine ⟨19433911120823846184698573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12955940747215897456465715 19433911120823846184698573)
              ·
                refine ⟨7287716670308942319261965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19433911120823846184698573 7287716670308942319261965)
                ·
                  refine ⟨2732893751365853369723237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7287716670308942319261965 2732893751365853369723237)
                  ·
                    refine ⟨512417578381097506823107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2732893751365853369723237 512417578381097506823107)
                    ·
                      rfl

theorem cell23_2993789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2993789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993789 prefixEnd_2993789 := by exact prefixLift 2993789
  have htrace : WordTrace (prefixWord ++ tailWord_2993789) baseStart_2993789 baseEnd_2993789 := by
    simpa [prefixWord, tailWord_2993789, baseEnd_2993789] using wordTrace_append hprefix tailTrace_2993789
  have hstable : (prefixWord ++ tailWord_2993789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993789).length < 2 ^ (prefixWord ++ tailWord_2993789).sum := by decide
  have hdescent : baseEnd_2993789 < baseStart_2993789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993829 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_2993829 : Nat := 118140960795 + 2993829 * 2 ^ 59
def prefixEnd_2993829 : Nat := 4983230072969 + 3 ^ 40 * 2993829 * 2
def baseEnd_2993829 : Nat := 1537273274369472363969137

theorem tailTrace_2993829 : CollatzResearch.WordTrace tailWord_2993829 prefixEnd_2993829 1537273274369472363969137 := by
  unfold tailWord_2993829
  simp only [CollatzResearch.WordTrace]
  refine ⟨109193914270876313131216541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72795942847250875420811027 109193914270876313131216541)
  ·
    refine ⟨40947717851578617424206203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109193914270876313131216541 40947717851578617424206203)
    ·
      refine ⟨61421576777367926136309305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40947717851578617424206203 61421576777367926136309305)
      ·
        refine ⟨46066182583025944602231979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61421576777367926136309305 46066182583025944602231979)
        ·
          refine ⟨69099273874538916903347969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46066182583025944602231979 69099273874538916903347969)
          ·
            refine ⟨51824455405904187677510977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69099273874538916903347969 51824455405904187677510977)
            ·
              refine ⟨38868341554428140758133233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51824455405904187677510977 38868341554428140758133233)
              ·
                refine ⟨29151256165821105568599925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38868341554428140758133233 29151256165821105568599925)
                ·
                  refine ⟨2732930265545728647056243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29151256165821105568599925 2732930265545728647056243)
                  ·
                    refine ⟨4099395398318592970584365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2732930265545728647056243 4099395398318592970584365)
                    ·
                      refine ⟨1537273274369472363969137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099395398318592970584365 1537273274369472363969137)
                      ·
                        rfl

theorem cell23_2993829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_2993829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993829 prefixEnd_2993829 := by exact prefixLift 2993829
  have htrace : WordTrace (prefixWord ++ tailWord_2993829) baseStart_2993829 baseEnd_2993829 := by
    simpa [prefixWord, tailWord_2993829, baseEnd_2993829] using wordTrace_append hprefix tailTrace_2993829
  have hstable : (prefixWord ++ tailWord_2993829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993829).length < 2 ^ (prefixWord ++ tailWord_2993829).sum := by decide
  have hdescent : baseEnd_2993829 < baseStart_2993829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993896 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2993896 : Nat := 118140960795 + 2993896 * 2 ^ 59
def prefixEnd_2993896 : Nat := 4983230072969 + 3 ^ 40 * 2993896 * 2
def baseEnd_2993896 : Nat := 512435892524441200610443

theorem tailTrace_2993896 : CollatzResearch.WordTrace tailWord_2993896 prefixEnd_2993896 512435892524441200610443 := by
  unfold tailWord_2993896
  simp only [CollatzResearch.WordTrace]
  refine ⟨54598178980816791786952771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72797571974422389049270361 54598178980816791786952771)
  ·
    refine ⟨81897268471225187680429157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54598178980816791786952771 81897268471225187680429157)
    ·
      refine ⟨15355737838354722690080467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81897268471225187680429157 15355737838354722690080467)
      ·
        refine ⟨23033606757532084035120701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15355737838354722690080467 23033606757532084035120701)
        ·
          refine ⟨8637602534074531513170263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23033606757532084035120701 8637602534074531513170263)
          ·
            refine ⟨12956403801111797269755395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8637602534074531513170263 12956403801111797269755395)
            ·
              refine ⟨19434605701667695904633093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12956403801111797269755395 19434605701667695904633093)
              ·
                refine ⟨3643988569062692982118705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19434605701667695904633093 3643988569062692982118705)
                ·
                  refine ⟨2732991426797019736589029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643988569062692982118705 2732991426797019736589029)
                  ·
                    refine ⟨512435892524441200610443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2732991426797019736589029 512435892524441200610443)
                    ·
                      rfl

theorem cell23_2993896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2993896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993896 prefixEnd_2993896 := by exact prefixLift 2993896
  have htrace : WordTrace (prefixWord ++ tailWord_2993896) baseStart_2993896 baseEnd_2993896 := by
    simpa [prefixWord, tailWord_2993896, baseEnd_2993896] using wordTrace_append hprefix tailTrace_2993896
  have hstable : (prefixWord ++ tailWord_2993896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993896).length < 2 ^ (prefixWord ++ tailWord_2993896).sum := by decide
  have hdescent : baseEnd_2993896 < baseStart_2993896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993919 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_2993919 : Nat := 118140960795 + 2993919 * 2 ^ 59
def prefixEnd_2993919 : Nat := 4983230072969 + 3 ^ 40 * 2993919 * 2
def baseEnd_2993919 : Nat := 1537319487628377011843723

theorem tailTrace_2993919 : CollatzResearch.WordTrace tailWord_2993919 prefixEnd_2993919 1537319487628377011843723 := by
  unfold tailWord_2993919
  simp only [CollatzResearch.WordTrace]
  refine ⟨109197196840550258501992811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72798131227033505667995207 109197196840550258501992811)
  ·
    refine ⟨163795795260825387752989217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109197196840550258501992811 163795795260825387752989217)
    ·
      refine ⟨122846846445619040814741913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163795795260825387752989217 122846846445619040814741913)
      ·
        refine ⟨92135134834214280611056435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122846846445619040814741913 92135134834214280611056435)
        ·
          refine ⟨138202702251321420916584653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92135134834214280611056435 138202702251321420916584653)
          ·
            refine ⟨51826013344245532843719245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138202702251321420916584653 51826013344245532843719245)
            ·
              refine ⟨19434755004092074816394717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51826013344245532843719245 19434755004092074816394717)
              ·
                refine ⟨7288033126534528056148019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19434755004092074816394717 7288033126534528056148019)
                ·
                  refine ⟨10932049689801792084222029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288033126534528056148019 10932049689801792084222029)
                  ·
                    refine ⟨4099518633675672031583261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10932049689801792084222029 4099518633675672031583261)
                    ·
                      refine ⟨1537319487628377011843723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099518633675672031583261 1537319487628377011843723)
                      ·
                        rfl

theorem cell23_2993919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_2993919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993919 prefixEnd_2993919 := by exact prefixLift 2993919
  have htrace : WordTrace (prefixWord ++ tailWord_2993919) baseStart_2993919 baseEnd_2993919 := by
    simpa [prefixWord, tailWord_2993919, baseEnd_2993919] using wordTrace_append hprefix tailTrace_2993919
  have hstable : (prefixWord ++ tailWord_2993919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993919).length < 2 ^ (prefixWord ++ tailWord_2993919).sum := by decide
  have hdescent : baseEnd_2993919 < baseStart_2993919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993953 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2993953 : Nat := 118140960795 + 2993953 * 2 ^ 59
def prefixEnd_2993953 : Nat := 4983230072969 + 3 ^ 40 * 2993953 * 2
def baseEnd_2993953 : Nat := 1537336945970629878818567

theorem tailTrace_2993953 : CollatzResearch.WordTrace tailWord_2993953 prefixEnd_2993953 1537336945970629878818567 := by
  unfold tailWord_2993953
  simp only [CollatzResearch.WordTrace]
  refine ⟨109198436922427082308730513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72798957948284721539153675 109198436922427082308730513)
  ·
    refine ⟨81898827691820311731547885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109198436922427082308730513 81898827691820311731547885)
    ·
      refine ⟨30712060384432616899330457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81898827691820311731547885 30712060384432616899330457)
      ·
        refine ⟨23034045288324462674497843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30712060384432616899330457 23034045288324462674497843)
        ·
          refine ⟨34551067932486694011746765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23034045288324462674497843 34551067932486694011746765)
          ·
            refine ⟨12956650474682510254405037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34551067932486694011746765 12956650474682510254405037)
            ·
              refine ⟨4858743928005941345401889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12956650474682510254405037 4858743928005941345401889)
              ·
                refine ⟨3644057946004456009051417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858743928005941345401889 3644057946004456009051417)
                ·
                  refine ⟨2733043459503342006788563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644057946004456009051417 2733043459503342006788563)
                  ·
                    refine ⟨4099565189255013010182845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733043459503342006788563 4099565189255013010182845)
                    ·
                      refine ⟨1537336945970629878818567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099565189255013010182845 1537336945970629878818567)
                      ·
                        rfl

theorem cell23_2993953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2993953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993953 prefixEnd_2993953 := by exact prefixLift 2993953
  have htrace : WordTrace (prefixWord ++ tailWord_2993953) baseStart_2993953 baseEnd_2993953 := by
    simpa [prefixWord, tailWord_2993953, baseEnd_2993953] using wordTrace_append hprefix tailTrace_2993953
  have hstable : (prefixWord ++ tailWord_2993953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993953).length < 2 ^ (prefixWord ++ tailWord_2993953).sum := by decide
  have hdescent : baseEnd_2993953 < baseStart_2993953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993969 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_2993969 : Nat := 118140960795 + 2993969 * 2 ^ 59
def prefixEnd_2993969 : Nat := 4983230072969 + 3 ^ 40 * 2993969 * 2
def baseEnd_2993969 : Nat := 512448387220367272072831

theorem tailTrace_2993969 : CollatzResearch.WordTrace tailWord_2993969 prefixEnd_2993969 512448387220367272072831 := by
  unfold tailWord_2993969
  simp only [CollatzResearch.WordTrace]
  refine ⟨109199020490369117041312961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72799346993579411360875307 109199020490369117041312961)
  ·
    refine ⟨81899265367776837780984721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109199020490369117041312961 81899265367776837780984721)
    ·
      refine ⟨61424449025832628335738541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81899265367776837780984721 61424449025832628335738541)
      ·
        refine ⟨23034168384687235625901953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61424449025832628335738541 23034168384687235625901953)
        ·
          refine ⟨17275626288515426719426465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23034168384687235625901953 17275626288515426719426465)
          ·
            refine ⟨12956719716386570039569849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17275626288515426719426465 12956719716386570039569849)
            ·
              refine ⟨9717539787289927529677387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12956719716386570039569849 9717539787289927529677387)
              ·
                refine ⟨14576309680934891294516081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717539787289927529677387 14576309680934891294516081)
                ·
                  refine ⟨10932232260701168470887061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14576309680934891294516081 10932232260701168470887061)
                  ·
                    refine ⟨512448387220367272072831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10932232260701168470887061 512448387220367272072831)
                    ·
                      rfl

theorem cell23_2993969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_2993969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993969 prefixEnd_2993969 := by exact prefixLift 2993969
  have htrace : WordTrace (prefixWord ++ tailWord_2993969) baseStart_2993969 baseEnd_2993969 := by
    simpa [prefixWord, tailWord_2993969, baseEnd_2993969] using wordTrace_append hprefix tailTrace_2993969
  have hstable : (prefixWord ++ tailWord_2993969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993969).length < 2 ^ (prefixWord ++ tailWord_2993969).sum := by decide
  have hdescent : baseEnd_2993969 < baseStart_2993969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993970 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_2993970 : Nat := 118140960795 + 2993970 * 2 ^ 59
def prefixEnd_2993970 : Nat := 4983230072969 + 3 ^ 40 * 2993970 * 2
def baseEnd_2993970 : Nat := 1537345675141756312305989

theorem tailTrace_2993970 : CollatzResearch.WordTrace tailWord_2993970 prefixEnd_2993970 1537345675141756312305989 := by
  unfold tailWord_2993970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27299764240841373553024841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72799371308910329474732909 27299764240841373553024841)
  ·
    refine ⟨20474823180631030164768631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27299764240841373553024841 20474823180631030164768631)
    ·
      refine ⟨30712234770946545247152947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20474823180631030164768631 30712234770946545247152947)
      ·
        refine ⟨46068352156419817870729421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30712234770946545247152947 46068352156419817870729421)
        ·
          refine ⟨17275632058657431701523533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46068352156419817870729421 17275632058657431701523533)
          ·
            refine ⟨6478362021996536888071325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17275632058657431701523533 6478362021996536888071325)
            ·
              refine ⟨2429385758248701333026747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6478362021996536888071325 2429385758248701333026747)
              ·
                refine ⟨3644078637373051999540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429385758248701333026747 3644078637373051999540121)
                ·
                  refine ⟨2733058978029788999655091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644078637373051999540121 2733058978029788999655091)
                  ·
                    refine ⟨4099588467044683499482637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733058978029788999655091 4099588467044683499482637)
                    ·
                      refine ⟨1537345675141756312305989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099588467044683499482637 1537345675141756312305989)
                      ·
                        rfl

theorem cell23_2993970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_2993970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993970 prefixEnd_2993970 := by exact prefixLift 2993970
  have htrace : WordTrace (prefixWord ++ tailWord_2993970) baseStart_2993970 baseEnd_2993970 := by
    simpa [prefixWord, tailWord_2993970, baseEnd_2993970] using wordTrace_append hprefix tailTrace_2993970
  have hstable : (prefixWord ++ tailWord_2993970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993970).length < 2 ^ (prefixWord ++ tailWord_2993970).sum := by decide
  have hdescent : baseEnd_2993970 < baseStart_2993970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993996 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2993996 : Nat := 118140960795 + 2993996 * 2 ^ 59
def prefixEnd_2993996 : Nat := 4983230072969 + 3 ^ 40 * 2993996 * 2
def baseEnd_2993996 : Nat := 1537359025638773210580869

theorem tailTrace_2993996 : CollatzResearch.WordTrace tailWord_2993996 prefixEnd_2993996 1537359025638773210580869 := by
  unfold tailWord_2993996
  simp only [CollatzResearch.WordTrace]
  refine ⟨54600002630635650326272921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72800003507514200435030561 54600002630635650326272921)
  ·
    refine ⟨40950001972976737744704691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54600002630635650326272921 40950001972976737744704691)
    ·
      refine ⟨61425002959465106617057037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40950001972976737744704691 61425002959465106617057037)
      ·
        refine ⟨23034376109799414981396389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61425002959465106617057037 23034376109799414981396389)
        ·
          refine ⟨4318945520587390309011823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23034376109799414981396389 4318945520587390309011823)
          ·
            refine ⟨6478418280881085463517735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318945520587390309011823 6478418280881085463517735)
            ·
              refine ⟨9717627421321628195276603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478418280881085463517735 9717627421321628195276603)
              ·
                refine ⟨14576441131982442292914905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717627421321628195276603 14576441131982442292914905)
                ·
                  refine ⟨10932330848986831719686179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14576441131982442292914905 10932330848986831719686179)
                  ·
                    refine ⟨16398496273480247579529269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10932330848986831719686179 16398496273480247579529269)
                    ·
                      refine ⟨1537359025638773210580869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16398496273480247579529269 1537359025638773210580869)
                      ·
                        rfl

theorem cell23_2993996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2993996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993996 prefixEnd_2993996 := by exact prefixLift 2993996
  have htrace : WordTrace (prefixWord ++ tailWord_2993996) baseStart_2993996 baseEnd_2993996 := by
    simpa [prefixWord, tailWord_2993996, baseEnd_2993996] using wordTrace_append hprefix tailTrace_2993996
  have hstable : (prefixWord ++ tailWord_2993996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993996).length < 2 ^ (prefixWord ++ tailWord_2993996).sum := by decide
  have hdescent : baseEnd_2993996 < baseStart_2993996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994016 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 7]
def baseStart_2994016 : Nat := 118140960795 + 2994016 * 2 ^ 59
def prefixEnd_2994016 : Nat := 4983230072969 + 3 ^ 40 * 2994016 * 2
def baseEnd_2994016 : Nat := 170818810583540348036753

theorem tailTrace_2994016 : CollatzResearch.WordTrace tailWord_2994016 prefixEnd_2994016 170818810583540348036753 := by
  unfold tailWord_2994016
  simp only [CollatzResearch.WordTrace]
  refine ⟨54600367360599422034136951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72800489814132562712182601 54600367360599422034136951)
  ·
    refine ⟨81900551040899133051205427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54600367360599422034136951 81900551040899133051205427)
    ·
      refine ⟨122850826561348699576808141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81900551040899133051205427 122850826561348699576808141)
      ·
        refine ⟨46069059960505762341303053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122850826561348699576808141 46069059960505762341303053)
        ·
          refine ⟨17275897485189660877988645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46069059960505762341303053 17275897485189660877988645)
          ·
            refine ⟨3239230778473061414622871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17275897485189660877988645 3239230778473061414622871)
            ·
              refine ⟨4858846167709592121934307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239230778473061414622871 4858846167709592121934307)
              ·
                refine ⟨7288269251564388182901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4858846167709592121934307 7288269251564388182901461)
                ·
                  refine ⟨170818810583540348036753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7288269251564388182901461 170818810583540348036753)
                  ·
                    rfl

theorem cell23_2994016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_2994016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994016 prefixEnd_2994016 := by exact prefixLift 2994016
  have htrace : WordTrace (prefixWord ++ tailWord_2994016) baseStart_2994016 baseEnd_2994016 := by
    simpa [prefixWord, tailWord_2994016, baseEnd_2994016] using wordTrace_append hprefix tailTrace_2994016
  have hstable : (prefixWord ++ tailWord_2994016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994016).length < 2 ^ (prefixWord ++ tailWord_2994016).sum := by decide
  have hdescent : baseEnd_2994016 < baseStart_2994016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994029 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2994029 : Nat := 118140960795 + 2994029 * 2 ^ 59
def prefixEnd_2994029 : Nat := 4983230072969 + 3 ^ 40 * 2994029 * 2
def baseEnd_2994029 : Nat := 512458656833457193822739

theorem tailTrace_2994029 : CollatzResearch.WordTrace tailWord_2994029 prefixEnd_2994029 512458656833457193822739 := by
  unfold tailWord_2994029
  simp only [CollatzResearch.WordTrace]
  refine ⟨109201208870151747288497141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72800805913434498192331427 109201208870151747288497141)
  ·
    refine ⟨10237613331576726308296607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109201208870151747288497141 10237613331576726308296607)
    ·
      refine ⟨15356419997365089462444911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10237613331576726308296607 15356419997365089462444911)
      ·
        refine ⟨23034629996047634193667367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15356419997365089462444911 23034629996047634193667367)
        ·
          refine ⟨34551944994071451290501051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23034629996047634193667367 34551944994071451290501051)
          ·
            refine ⟨51827917491107176935751577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34551944994071451290501051 51827917491107176935751577)
            ·
              refine ⟨38870938118330382701813683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51827917491107176935751577 38870938118330382701813683)
              ·
                refine ⟨58306407177495574052720525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38870938118330382701813683 58306407177495574052720525)
                ·
                  refine ⟨21864902691560840269770197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58306407177495574052720525 21864902691560840269770197)
                  ·
                    refine ⟨512458656833457193822739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21864902691560840269770197 512458656833457193822739)
                    ·
                      rfl

theorem cell23_2994029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2994029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994029 prefixEnd_2994029 := by exact prefixLift 2994029
  have htrace : WordTrace (prefixWord ++ tailWord_2994029) baseStart_2994029 baseEnd_2994029 := by
    simpa [prefixWord, tailWord_2994029, baseEnd_2994029] using wordTrace_append hprefix tailTrace_2994029
  have hstable : (prefixWord ++ tailWord_2994029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994029).length < 2 ^ (prefixWord ++ tailWord_2994029).sum := by decide
  have hdescent : baseEnd_2994029 < baseStart_2994029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994069 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2994069 : Nat := 118140960795 + 2994069 * 2 ^ 59
def prefixEnd_2994069 : Nat := 4983230072969 + 3 ^ 40 * 2994069 * 2
def baseEnd_2994069 : Nat := 1537396509726551424968033

theorem tailTrace_2994069 : CollatzResearch.WordTrace tailWord_2994069 prefixEnd_2994069 1537396509726551424968033 := by
  unfold tailWord_2994069
  simp only [CollatzResearch.WordTrace]
  refine ⟨109202667790006834119953261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72801778526671222746635507 109202667790006834119953261)
  ·
    refine ⟨40951000421252562794982473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109202667790006834119953261 40951000421252562794982473)
    ·
      refine ⟨30713250315939422096236855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40951000421252562794982473 30713250315939422096236855)
      ·
        refine ⟨46069875473909133144355283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30713250315939422096236855 46069875473909133144355283)
        ·
          refine ⟨69104813210863699716532925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46069875473909133144355283 69104813210863699716532925)
          ·
            refine ⟨25914304954073887393699847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69104813210863699716532925 25914304954073887393699847)
            ·
              refine ⟨38871457431110831090549771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25914304954073887393699847 38871457431110831090549771)
              ·
                refine ⟨58307186146666246635824657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38871457431110831090549771 58307186146666246635824657)
                ·
                  refine ⟨43730389609999684976868493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58307186146666246635824657 43730389609999684976868493)
                  ·
                    refine ⟨16398896103749881866325685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43730389609999684976868493 16398896103749881866325685)
                    ·
                      refine ⟨1537396509726551424968033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16398896103749881866325685 1537396509726551424968033)
                      ·
                        rfl

theorem cell23_2994069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2994069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994069 prefixEnd_2994069 := by exact prefixLift 2994069
  have htrace : WordTrace (prefixWord ++ tailWord_2994069) baseStart_2994069 baseEnd_2994069 := by
    simpa [prefixWord, tailWord_2994069, baseEnd_2994069] using wordTrace_append hprefix tailTrace_2994069
  have hstable : (prefixWord ++ tailWord_2994069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994069).length < 2 ^ (prefixWord ++ tailWord_2994069).sum := by decide
  have hdescent : baseEnd_2994069 < baseStart_2994069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994100 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2994100 : Nat := 118140960795 + 2994100 * 2 ^ 59
def prefixEnd_2994100 : Nat := 4983230072969 + 3 ^ 40 * 2994100 * 2
def baseEnd_2994100 : Nat := 1537412427626840803680391

theorem tailTrace_2994100 : CollatzResearch.WordTrace tailWord_2994100 prefixEnd_2994100 1537412427626840803680391 := by
  unfold tailWord_2994100
  simp only [CollatzResearch.WordTrace]
  refine ⟨54601899226447263207165877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72802532301929684276221169 54601899226447263207165877)
  ·
    refine ⟨5118928052479430925671801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54601899226447263207165877 5118928052479430925671801)
    ·
      refine ⟨3839196039359573194253851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5118928052479430925671801 3839196039359573194253851)
      ·
        refine ⟨5758794059039359791380777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839196039359573194253851 5758794059039359791380777)
        ·
          refine ⟨4319095544279519843535583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758794059039359791380777 4319095544279519843535583)
          ·
            refine ⟨6478643316419279765303375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319095544279519843535583 6478643316419279765303375)
            ·
              refine ⟨9717964974628919647955063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478643316419279765303375 9717964974628919647955063)
              ·
                refine ⟨14576947461943379471932595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717964974628919647955063 14576947461943379471932595)
                ·
                  refine ⟨21865421192915069207898893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14576947461943379471932595 21865421192915069207898893)
                  ·
                    refine ⟨8199532947343150952962085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21865421192915069207898893 8199532947343150952962085)
                    ·
                      refine ⟨1537412427626840803680391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8199532947343150952962085 1537412427626840803680391)
                      ·
                        rfl

theorem cell23_2994100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2994100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994100 prefixEnd_2994100 := by exact prefixLift 2994100
  have htrace : WordTrace (prefixWord ++ tailWord_2994100) baseStart_2994100 baseEnd_2994100 := by
    simpa [prefixWord, tailWord_2994100, baseEnd_2994100] using wordTrace_append hprefix tailTrace_2994100
  have hstable : (prefixWord ++ tailWord_2994100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994100).length < 2 ^ (prefixWord ++ tailWord_2994100).sum := by decide
  have hdescent : baseEnd_2994100 < baseStart_2994100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994110 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2994110 : Nat := 118140960795 + 2994110 * 2 ^ 59
def prefixEnd_2994110 : Nat := 4983230072969 + 3 ^ 40 * 2994110 * 2
def baseEnd_2994110 : Nat := 512472520811128588185115

theorem tailTrace_2994110 : CollatzResearch.WordTrace tailWord_2994110 prefixEnd_2994110 512472520811128588185115 := by
  unfold tailWord_2994110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650520397857287265274473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72802775455238865414797189 13650520397857287265274473)
  ·
    refine ⟨10237890298392965448955855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13650520397857287265274473 10237890298392965448955855)
    ·
      refine ⟨15356835447589448173433783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10237890298392965448955855 15356835447589448173433783)
      ·
        refine ⟨23035253171384172260150675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15356835447589448173433783 23035253171384172260150675)
        ·
          refine ⟨34552879757076258390226013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23035253171384172260150675 34552879757076258390226013)
          ·
            refine ⟨12957329908903596896334755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34552879757076258390226013 12957329908903596896334755)
            ·
              refine ⟨19435994863355395344502133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12957329908903596896334755 19435994863355395344502133)
              ·
                refine ⟨1822124518439568313547075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19435994863355395344502133 1822124518439568313547075)
                ·
                  refine ⟨2733186777659352470320613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822124518439568313547075 2733186777659352470320613)
                  ·
                    refine ⟨512472520811128588185115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2733186777659352470320613 512472520811128588185115)
                    ·
                      rfl

theorem cell23_2994110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2994110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994110 prefixEnd_2994110 := by exact prefixLift 2994110
  have htrace : WordTrace (prefixWord ++ tailWord_2994110) baseStart_2994110 baseEnd_2994110 := by
    simpa [prefixWord, tailWord_2994110, baseEnd_2994110] using wordTrace_append hprefix tailTrace_2994110
  have hstable : (prefixWord ++ tailWord_2994110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994110).length < 2 ^ (prefixWord ++ tailWord_2994110).sum := by decide
  have hdescent : baseEnd_2994110 < baseStart_2994110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994129 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2994129 : Nat := 118140960795 + 2994129 * 2 ^ 59
def prefixEnd_2994129 : Nat := 4983230072969 + 3 ^ 40 * 2994129 * 2
def baseEnd_2994129 : Nat := 1537427318565821190217757

theorem tailTrace_2994129 : CollatzResearch.WordTrace tailWord_2994129 prefixEnd_2994129 1537427318565821190217757 := by
  unfold tailWord_2994129
  simp only [CollatzResearch.WordTrace]
  refine ⟨109204856169789464367137441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72803237446526309578091627 109204856169789464367137441)
  ·
    refine ⟨81903642127342098275353081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109204856169789464367137441 81903642127342098275353081)
    ·
      refine ⟨61427731595506573706514811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81903642127342098275353081 61427731595506573706514811)
      ·
        refine ⟨92141597393259860559772217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61427731595506573706514811 92141597393259860559772217)
        ·
          refine ⟨69106198044944895419829163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92141597393259860559772217 69106198044944895419829163)
          ·
            refine ⟨103659297067417343129743745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69106198044944895419829163 103659297067417343129743745)
            ·
              refine ⟨77744472800563007347307809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103659297067417343129743745 77744472800563007347307809)
              ·
                refine ⟨58308354600422255510480857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77744472800563007347307809 58308354600422255510480857)
                ·
                  refine ⟨43731265950316691632860643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58308354600422255510480857 43731265950316691632860643)
                  ·
                    refine ⟨65596898925475037449290965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43731265950316691632860643 65596898925475037449290965)
                    ·
                      refine ⟨1537427318565821190217757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65596898925475037449290965 1537427318565821190217757)
                      ·
                        rfl

theorem cell23_2994129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2994129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994129 prefixEnd_2994129 := by exact prefixLift 2994129
  have htrace : WordTrace (prefixWord ++ tailWord_2994129) baseStart_2994129 baseEnd_2994129 := by
    simpa [prefixWord, tailWord_2994129, baseEnd_2994129] using wordTrace_append hprefix tailTrace_2994129
  have hstable : (prefixWord ++ tailWord_2994129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994129).length < 2 ^ (prefixWord ++ tailWord_2994129).sum := by decide
  have hdescent : baseEnd_2994129 < baseStart_2994129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994143 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 1, 5, 2]
def baseStart_2994143 : Nat := 118140960795 + 2994143 * 2 ^ 59
def prefixEnd_2994143 : Nat := 4983230072969 + 3 ^ 40 * 2994143 * 2
def baseEnd_2994143 : Nat := 1537434507294984135442693

theorem tailTrace_2994143 : CollatzResearch.WordTrace tailWord_2994143 prefixEnd_2994143 1537434507294984135442693 := by
  unfold tailWord_2994143
  simp only [CollatzResearch.WordTrace]
  refine ⟨109205366791738744758147083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72803577861159163172098055 109205366791738744758147083)
  ·
    refine ⟨163808050187608117137220625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109205366791738744758147083 163808050187608117137220625)
    ·
      refine ⟨122856037640706087852915469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163808050187608117137220625 122856037640706087852915469)
      ·
        refine ⟨46071014115264782944843301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122856037640706087852915469 46071014115264782944843301)
        ·
          refine ⟨8638315146612146802158119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46071014115264782944843301 8638315146612146802158119)
          ·
            refine ⟨12957472719918220203237179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638315146612146802158119 12957472719918220203237179)
            ·
              refine ⟨19436209079877330304855769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12957472719918220203237179 19436209079877330304855769)
              ·
                refine ⟨14577156809907997728641827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19436209079877330304855769 14577156809907997728641827)
                ·
                  refine ⟨21865735214861996592962741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14577156809907997728641827 21865735214861996592962741)
                  ·
                    refine ⟨2049912676393312180590257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21865735214861996592962741 2049912676393312180590257)
                    ·
                      refine ⟨1537434507294984135442693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049912676393312180590257 1537434507294984135442693)
                      ·
                        rfl

theorem cell23_2994143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_2994143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994143 prefixEnd_2994143 := by exact prefixLift 2994143
  have htrace : WordTrace (prefixWord ++ tailWord_2994143) baseStart_2994143 baseEnd_2994143 := by
    simpa [prefixWord, tailWord_2994143, baseEnd_2994143] using wordTrace_append hprefix tailTrace_2994143
  have hstable : (prefixWord ++ tailWord_2994143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994143).length < 2 ^ (prefixWord ++ tailWord_2994143).sum := by decide
  have hdescent : baseEnd_2994143 < baseStart_2994143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994156 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_2994156 : Nat := 118140960795 + 2994156 * 2 ^ 59
def prefixEnd_2994156 : Nat := 4983230072969 + 3 ^ 40 * 2994156 * 2
def baseEnd_2994156 : Nat := 1537441182543492584580133

theorem tailTrace_2994156 : CollatzResearch.WordTrace tailWord_2994156 prefixEnd_2994156 1537441182543492584580133 := by
  unfold tailWord_2994156
  simp only [CollatzResearch.WordTrace]
  refine ⟨54602920470345823989185161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72803893960461098652246881 54602920470345823989185161)
  ·
    refine ⟨40952190352759367991888871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54602920470345823989185161 40952190352759367991888871)
    ·
      refine ⟨61428285529139051987833307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40952190352759367991888871 61428285529139051987833307)
      ·
        refine ⟨92142428293708577981749961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61428285529139051987833307 92142428293708577981749961)
        ·
          refine ⟨69106821220281433486312471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92142428293708577981749961 69106821220281433486312471)
          ·
            refine ⟨103660231830422150229468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69106821220281433486312471 103660231830422150229468707)
            ·
              refine ⟨155490347745633225344203061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103660231830422150229468707 155490347745633225344203061)
              ·
                refine ⟨14577220101153114876019037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155490347745633225344203061 14577220101153114876019037)
                ·
                  refine ⟨5466457537932418078507139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14577220101153114876019037 5466457537932418078507139)
                  ·
                    refine ⟨8199686306898627117760709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466457537932418078507139 8199686306898627117760709)
                    ·
                      refine ⟨1537441182543492584580133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8199686306898627117760709 1537441182543492584580133)
                      ·
                        rfl

theorem cell23_2994156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_2994156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994156 prefixEnd_2994156 := by exact prefixLift 2994156
  have htrace : WordTrace (prefixWord ++ tailWord_2994156) baseStart_2994156 baseEnd_2994156 := by
    simpa [prefixWord, tailWord_2994156, baseEnd_2994156] using wordTrace_append hprefix tailTrace_2994156
  have hstable : (prefixWord ++ tailWord_2994156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994156).length < 2 ^ (prefixWord ++ tailWord_2994156).sum := by decide
  have hdescent : baseEnd_2994156 < baseStart_2994156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994173 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_2994173 : Nat := 118140960795 + 2994173 * 2 ^ 59
def prefixEnd_2994173 : Nat := 4983230072969 + 3 ^ 40 * 2994173 * 2
def baseEnd_2994173 : Nat := 1537449911714619018067555

theorem tailTrace_2994173 : CollatzResearch.WordTrace tailWord_2994173 prefixEnd_2994173 1537449911714619018067555 := by
  unfold tailWord_2994173
  simp only [CollatzResearch.WordTrace]
  refine ⟨109206460981630059881739173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72804307321086706587826115 109206460981630059881739173)
  ·
    refine ⟨20476211434055636227826095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109206460981630059881739173 20476211434055636227826095)
    ·
      refine ⟨30714317151083454341739143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20476211434055636227826095 30714317151083454341739143)
      ·
        refine ⟨46071475726625181512608715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30714317151083454341739143 46071475726625181512608715)
        ·
          refine ⟨69107213589937772268913073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46071475726625181512608715 69107213589937772268913073)
          ·
            refine ⟨51830410192453329201684805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69107213589937772268913073 51830410192453329201684805)
            ·
              refine ⟨9718201911084999225315901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51830410192453329201684805 9718201911084999225315901)
              ·
                refine ⟨3644325716656874709493463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9718201911084999225315901 3644325716656874709493463)
                ·
                  refine ⟨5466488574985312064240195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644325716656874709493463 5466488574985312064240195)
                  ·
                    refine ⟨8199732862477968096360293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5466488574985312064240195 8199732862477968096360293)
                    ·
                      refine ⟨1537449911714619018067555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8199732862477968096360293 1537449911714619018067555)
                      ·
                        rfl

theorem cell23_2994173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_2994173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994173 prefixEnd_2994173 := by exact prefixLift 2994173
  have htrace : WordTrace (prefixWord ++ tailWord_2994173) baseStart_2994173 baseEnd_2994173 := by
    simpa [prefixWord, tailWord_2994173, baseEnd_2994173] using wordTrace_append hprefix tailTrace_2994173
  have hstable : (prefixWord ++ tailWord_2994173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994173).length < 2 ^ (prefixWord ++ tailWord_2994173).sum := by decide
  have hdescent : baseEnd_2994173 < baseStart_2994173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994183 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 4, 4]
def baseStart_2994183 : Nat := 118140960795 + 2994183 * 2 ^ 59
def prefixEnd_2994183 : Nat := 4983230072969 + 3 ^ 40 * 2994183 * 2
def baseEnd_2994183 : Nat := 512485015507054659647503

theorem tailTrace_2994183 : CollatzResearch.WordTrace tailWord_2994183 prefixEnd_2994183 512485015507054659647503 := by
  unfold tailWord_2994183
  simp only [CollatzResearch.WordTrace]
  refine ⟨109206825711593831589603203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72804550474395887726402135 109206825711593831589603203)
  ·
    refine ⟨163810238567390747384404805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109206825711593831589603203 163810238567390747384404805)
    ·
      refine ⟨30714419731385765134575901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163810238567390747384404805 30714419731385765134575901)
      ·
        refine ⟨11517907399269661925465963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30714419731385765134575901 11517907399269661925465963)
        ·
          refine ⟨17276861098904492888198945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11517907399269661925465963 17276861098904492888198945)
          ·
            refine ⟨12957645824178369666149209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17276861098904492888198945 12957645824178369666149209)
            ·
              refine ⟨9718234368133777249611907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12957645824178369666149209 9718234368133777249611907)
              ·
                refine ⟨14577351552200665874417861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9718234368133777249611907 14577351552200665874417861)
                ·
                  refine ⟨2733253416037624851453349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14577351552200665874417861 2733253416037624851453349)
                  ·
                    refine ⟨512485015507054659647503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2733253416037624851453349 512485015507054659647503)
                    ·
                      rfl

theorem cell23_2994183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_2994183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994183 prefixEnd_2994183 := by exact prefixLift 2994183
  have htrace : WordTrace (prefixWord ++ tailWord_2994183) baseStart_2994183 baseEnd_2994183 := by
    simpa [prefixWord, tailWord_2994183, baseEnd_2994183] using wordTrace_append hprefix tailTrace_2994183
  have hstable : (prefixWord ++ tailWord_2994183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994183).length < 2 ^ (prefixWord ++ tailWord_2994183).sum := by decide
  have hdescent : baseEnd_2994183 < baseStart_2994183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994223 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 3]
def baseStart_2994223 : Nat := 118140960795 + 2994223 * 2 ^ 59
def prefixEnd_2994223 : Nat := 4983230072969 + 3 ^ 40 * 2994223 * 2
def baseEnd_2994223 : Nat := 1537475585747343822442325

theorem tailTrace_2994223 : CollatzResearch.WordTrace tailWord_2994223 prefixEnd_2994223 1537475585747343822442325 := by
  unfold tailWord_2994223
  simp only [CollatzResearch.WordTrace]
  refine ⟨109208284631448918421059323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72805523087632612280706215 109208284631448918421059323)
  ·
    refine ⟨163812426947173377631588985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109208284631448918421059323 163812426947173377631588985)
    ·
      refine ⟨122859320210380033223691739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163812426947173377631588985 122859320210380033223691739)
      ·
        refine ⟨184288980315570049835537609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122859320210380033223691739 184288980315570049835537609)
        ·
          refine ⟨138216735236677537376653207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184288980315570049835537609 138216735236677537376653207)
          ·
            refine ⟨207325102855016306064979811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138216735236677537376653207 207325102855016306064979811)
            ·
              refine ⟨310987654282524459097469717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207325102855016306064979811 310987654282524459097469717)
              ·
                refine ⟨14577546294493334020193893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 310987654282524459097469717 14577546294493334020193893)
                ·
                  refine ⟨2733289930217500128786355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14577546294493334020193893 2733289930217500128786355)
                  ·
                    refine ⟨4099934895326250193179533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733289930217500128786355 4099934895326250193179533)
                    ·
                      refine ⟨1537475585747343822442325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099934895326250193179533 1537475585747343822442325)
                      ·
                        rfl

theorem cell23_2994223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_2994223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994223 prefixEnd_2994223 := by exact prefixLift 2994223
  have htrace : WordTrace (prefixWord ++ tailWord_2994223) baseStart_2994223 baseEnd_2994223 := by
    simpa [prefixWord, tailWord_2994223, baseEnd_2994223] using wordTrace_append hprefix tailTrace_2994223
  have hstable : (prefixWord ++ tailWord_2994223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994223).length < 2 ^ (prefixWord ++ tailWord_2994223).sum := by decide
  have hdescent : baseEnd_2994223 < baseStart_2994223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994240 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 2, 1, 3]
def baseStart_2994240 : Nat := 118140960795 + 2994240 * 2 ^ 59
def prefixEnd_2994240 : Nat := 4983230072969 + 3 ^ 40 * 2994240 * 2
def baseEnd_2994240 : Nat := 1537484314918470255929747

theorem tailTrace_2994240 : CollatzResearch.WordTrace tailWord_2994240 prefixEnd_2994240 1537484314918470255929747 := by
  unfold tailWord_2994240
  simp only [CollatzResearch.WordTrace]
  refine ⟨54604452336193665162214087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72805936448258220216285449 54604452336193665162214087)
  ·
    refine ⟨81906678504290497743321131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54604452336193665162214087 81906678504290497743321131)
    ·
      refine ⟨122860017756435746614981697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81906678504290497743321131 122860017756435746614981697)
      ·
        refine ⟨92145013317326809961236273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122860017756435746614981697 92145013317326809961236273)
        ·
          refine ⟨69108759987995107470927205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92145013317326809961236273 69108759987995107470927205)
          ·
            refine ⟨12957892497749082650798851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69108759987995107470927205 12957892497749082650798851)
            ·
              refine ⟨19436838746623623976198277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12957892497749082650798851 19436838746623623976198277)
              ·
                refine ⟨3644407264991929495537177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19436838746623623976198277 3644407264991929495537177)
                ·
                  refine ⟨2733305448743947121652883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644407264991929495537177 2733305448743947121652883)
                  ·
                    refine ⟨4099958173115920682479325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733305448743947121652883 4099958173115920682479325)
                    ·
                      refine ⟨1537484314918470255929747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4099958173115920682479325 1537484314918470255929747)
                      ·
                        rfl

theorem cell23_2994240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_2994240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994240 prefixEnd_2994240 := by exact prefixLift 2994240
  have htrace : WordTrace (prefixWord ++ tailWord_2994240) baseStart_2994240 baseEnd_2994240 := by
    simpa [prefixWord, tailWord_2994240, baseEnd_2994240] using wordTrace_append hprefix tailTrace_2994240
  have hstable : (prefixWord ++ tailWord_2994240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994240).length < 2 ^ (prefixWord ++ tailWord_2994240).sum := by decide
  have hdescent : baseEnd_2994240 < baseStart_2994240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994241 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_2994241 : Nat := 118140960795 + 2994241 * 2 ^ 59
def prefixEnd_2994241 : Nat := 4983230072969 + 3 ^ 40 * 2994241 * 2
def baseEnd_2994241 : Nat := 1537484828399124752017243

theorem tailTrace_2994241 : CollatzResearch.WordTrace tailWord_2994241 prefixEnd_2994241 1537484828399124752017243 := by
  unfold tailWord_2994241
  simp only [CollatzResearch.WordTrace]
  refine ⟨109208941145383707495214577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72805960763589138330143051 109208941145383707495214577)
  ·
    refine ⟨81906705859037780621410933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109208941145383707495214577 81906705859037780621410933)
    ·
      refine ⟨7678753674284791933257275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81906705859037780621410933 7678753674284791933257275)
      ·
        refine ⟨11518130511427187899885913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678753674284791933257275 11518130511427187899885913)
        ·
          refine ⟨8638597883570390924914435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11518130511427187899885913 8638597883570390924914435)
          ·
            refine ⟨12957896825355586387371653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638597883570390924914435 12957896825355586387371653)
            ·
              refine ⟨2429605654754172447632185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12957896825355586387371653 2429605654754172447632185)
              ·
                refine ⟨1822204241065629335724139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429605654754172447632185 1822204241065629335724139)
                ·
                  refine ⟨2733306361598444003586209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822204241065629335724139 2733306361598444003586209)
                  ·
                    refine ⟨2049979771198833002689657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2733306361598444003586209 2049979771198833002689657)
                    ·
                      refine ⟨1537484828399124752017243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049979771198833002689657 1537484828399124752017243)
                      ·
                        rfl

theorem cell23_2994241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_2994241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994241 prefixEnd_2994241 := by exact prefixLift 2994241
  have htrace : WordTrace (prefixWord ++ tailWord_2994241) baseStart_2994241 baseEnd_2994241 := by
    simpa [prefixWord, tailWord_2994241, baseEnd_2994241] using wordTrace_append hprefix tailTrace_2994241
  have hstable : (prefixWord ++ tailWord_2994241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994241).length < 2 ^ (prefixWord ++ tailWord_2994241).sum := by decide
  have hdescent : baseEnd_2994241 < baseStart_2994241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994284 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 1, 3, 2]
def baseStart_2994284 : Nat := 118140960795 + 2994284 * 2 ^ 59
def prefixEnd_2994284 : Nat := 4983230072969 + 3 ^ 40 * 2994284 * 2
def baseEnd_2994284 : Nat := 1537506908067268083779545

theorem tailTrace_2994284 : CollatzResearch.WordTrace tailWord_2994284 prefixEnd_2994284 1537506908067268083779545 := by
  unfold tailWord_2994284
  simp only [CollatzResearch.WordTrace]
  refine ⟨54605254742113962919514953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72807006322818617226019937 54605254742113962919514953)
  ·
    refine ⟨40953941056585472189636215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54605254742113962919514953 40953941056585472189636215)
    ·
      refine ⟨61430911584878208284454323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40953941056585472189636215 61430911584878208284454323)
      ·
        refine ⟨92146367377317312426681485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61430911584878208284454323 92146367377317312426681485)
        ·
          refine ⟨34554887766493992160005557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92146367377317312426681485 34554887766493992160005557)
          ·
            refine ⟨3239520728108811765000521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34554887766493992160005557 3239520728108811765000521)
            ·
              refine ⟨2429640546081608823750391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239520728108811765000521 2429640546081608823750391)
              ·
                refine ⟨3644460819122413235625587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429640546081608823750391 3644460819122413235625587)
                ·
                  refine ⟨5466691228683619853438381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644460819122413235625587 5466691228683619853438381)
                  ·
                    refine ⟨2050009210756357445039393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5466691228683619853438381 2050009210756357445039393)
                    ·
                      refine ⟨1537506908067268083779545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050009210756357445039393 1537506908067268083779545)
                      ·
                        rfl

theorem cell23_2994284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_2994284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994284 prefixEnd_2994284 := by exact prefixLift 2994284
  have htrace : WordTrace (prefixWord ++ tailWord_2994284) baseStart_2994284 baseEnd_2994284 := by
    simpa [prefixWord, tailWord_2994284, baseEnd_2994284] using wordTrace_append hprefix tailTrace_2994284
  have hstable : (prefixWord ++ tailWord_2994284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994284).length < 2 ^ (prefixWord ++ tailWord_2994284).sum := by decide
  have hdescent : baseEnd_2994284 < baseStart_2994284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994297 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 4, 2, 2]
def baseStart_2994297 : Nat := 118140960795 + 2994297 * 2 ^ 59
def prefixEnd_2994297 : Nat := 4983230072969 + 3 ^ 40 * 2994297 * 2
def baseEnd_2994297 : Nat := 1537513583315776532916985

theorem tailTrace_2994297 : CollatzResearch.WordTrace tailWord_2994297 prefixEnd_2994297 1537513583315776532916985 := by
  unfold tailWord_2994297
  simp only [CollatzResearch.WordTrace]
  refine ⟨109210983633180829059253145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72807322422120552706168763 109210983633180829059253145)
  ·
    refine ⟨81908237724885621794439859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109210983633180829059253145 81908237724885621794439859)
    ·
      refine ⟨122862356587328432691659789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81908237724885621794439859 122862356587328432691659789)
      ·
        refine ⟨46073383720248162259372421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122862356587328432691659789 46073383720248162259372421)
        ·
          refine ⟨8638759447546530423632329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46073383720248162259372421 8638759447546530423632329)
          ·
            refine ⟨6479069585659897817724247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638759447546530423632329 6479069585659897817724247)
            ·
              refine ⟨9718604378489846726586371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479069585659897817724247 9718604378489846726586371)
              ·
                refine ⟨14577906567734770089879557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9718604378489846726586371 14577906567734770089879557)
                ·
                  refine ⟨2733357481450269391852417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14577906567734770089879557 2733357481450269391852417)
                  ·
                    refine ⟨2050018111087702043889313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2733357481450269391852417 2050018111087702043889313)
                    ·
                      refine ⟨1537513583315776532916985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050018111087702043889313 1537513583315776532916985)
                      ·
                        rfl

theorem cell23_2994297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_2994297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994297 prefixEnd_2994297 := by exact prefixLift 2994297
  have htrace : WordTrace (prefixWord ++ tailWord_2994297) baseStart_2994297 baseEnd_2994297 := by
    simpa [prefixWord, tailWord_2994297, baseEnd_2994297] using wordTrace_append hprefix tailTrace_2994297
  have hstable : (prefixWord ++ tailWord_2994297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994297).length < 2 ^ (prefixWord ++ tailWord_2994297).sum := by decide
  have hdescent : baseEnd_2994297 < baseStart_2994297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994313 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_2994313 : Nat := 118140960795 + 2994313 * 2 ^ 59
def prefixEnd_2994313 : Nat := 4983230072969 + 3 ^ 40 * 2994313 * 2
def baseEnd_2994313 : Nat := 1537521799006248470316911

theorem tailTrace_2994313 : CollatzResearch.WordTrace tailWord_2994313 prefixEnd_2994313 1537521799006248470316911 := by
  unfold tailWord_2994313
  simp only [CollatzResearch.WordTrace]
  refine ⟨109211567201122863791835593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72807711467415242527890395 109211567201122863791835593)
  ·
    refine ⟨81908675400842147843876695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109211567201122863791835593 81908675400842147843876695)
    ·
      refine ⟨122863013101263221765815043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81908675400842147843876695 122863013101263221765815043)
      ·
        refine ⟨184294519651894832648722565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122863013101263221765815043 184294519651894832648722565)
        ·
          refine ⟨34555222434730281121635481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184294519651894832648722565 34555222434730281121635481)
          ·
            refine ⟨25916416826047710841226611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34555222434730281121635481 25916416826047710841226611)
            ·
              refine ⟨38874625239071566261839917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25916416826047710841226611 38874625239071566261839917)
              ·
                refine ⟨14577984464651837348189969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38874625239071566261839917 14577984464651837348189969)
                ·
                  refine ⟨10933488348488878011142477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14577984464651837348189969 10933488348488878011142477)
                  ·
                    refine ⟨4100058130683329254178429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10933488348488878011142477 4100058130683329254178429)
                    ·
                      refine ⟨1537521799006248470316911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100058130683329254178429 1537521799006248470316911)
                      ·
                        rfl

theorem cell23_2994313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_2994313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994313 prefixEnd_2994313 := by exact prefixLift 2994313
  have htrace : WordTrace (prefixWord ++ tailWord_2994313) baseStart_2994313 baseEnd_2994313 := by
    simpa [prefixWord, tailWord_2994313, baseEnd_2994313] using wordTrace_append hprefix tailTrace_2994313
  have hstable : (prefixWord ++ tailWord_2994313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994313).length < 2 ^ (prefixWord ++ tailWord_2994313).sum := by decide
  have hdescent : baseEnd_2994313 < baseStart_2994313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994333 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2994333 : Nat := 118140960795 + 2994333 * 2 ^ 59
def prefixEnd_2994333 : Nat := 4983230072969 + 3 ^ 40 * 2994333 * 2
def baseEnd_2994333 : Nat := 512510689539779464022273

theorem tailTrace_2994333 : CollatzResearch.WordTrace tailWord_2994333 prefixEnd_2994333 512510689539779464022273 := by
  unfold tailWord_2994333
  simp only [CollatzResearch.WordTrace]
  refine ⟨109212296661050407207563653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72808197774033604805042435 109212296661050407207563653)
  ·
    refine ⟨20477305623946951351418185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109212296661050407207563653 20477305623946951351418185)
    ·
      refine ⟨15357979217960213513563639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20477305623946951351418185 15357979217960213513563639)
      ·
        refine ⟨23036968826940320270345459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15357979217960213513563639 23036968826940320270345459)
        ·
          refine ⟨34555453240410480405518189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23036968826940320270345459 34555453240410480405518189)
          ·
            refine ⟨12958294965153930152069321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34555453240410480405518189 12958294965153930152069321)
            ·
              refine ⟨9718721223865447614051991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12958294965153930152069321 9718721223865447614051991)
              ·
                refine ⟨14578081835798171421077987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9718721223865447614051991 14578081835798171421077987)
                ·
                  refine ⟨21867122753697257131616981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14578081835798171421077987 21867122753697257131616981)
                  ·
                    refine ⟨512510689539779464022273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21867122753697257131616981 512510689539779464022273)
                    ·
                      rfl

theorem cell23_2994333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2994333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994333 prefixEnd_2994333 := by exact prefixLift 2994333
  have htrace : WordTrace (prefixWord ++ tailWord_2994333) baseStart_2994333 baseEnd_2994333 := by
    simpa [prefixWord, tailWord_2994333, baseEnd_2994333] using wordTrace_append hprefix tailTrace_2994333
  have hstable : (prefixWord ++ tailWord_2994333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994333).length < 2 ^ (prefixWord ++ tailWord_2994333).sum := by decide
  have hdescent : baseEnd_2994333 < baseStart_2994333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994337 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 5]
def baseStart_2994337 : Nat := 118140960795 + 2994337 * 2 ^ 59
def prefixEnd_2994337 : Nat := 4983230072969 + 3 ^ 40 * 2994337 * 2
def baseEnd_2994337 : Nat := 170837124726884041824089

theorem tailTrace_2994337 : CollatzResearch.WordTrace tailWord_2994337 prefixEnd_2994337 170837124726884041824089 := by
  unfold tailWord_2994337
  simp only [CollatzResearch.WordTrace]
  refine ⟨109212442553035915890709265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72808295035357277260472843 109212442553035915890709265)
  ·
    refine ⟨81909331914776936918031949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109212442553035915890709265 81909331914776936918031949)
    ·
      refine ⟨30715999468041351344261981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81909331914776936918031949 30715999468041351344261981)
      ·
        refine ⟨11518499800515506754098243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30715999468041351344261981 11518499800515506754098243)
        ·
          refine ⟨17277749700773260131147365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11518499800515506754098243 17277749700773260131147365)
          ·
            refine ⟨3239578068894986274590131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17277749700773260131147365 3239578068894986274590131)
            ·
              refine ⟨4859367103342479411885197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239578068894986274590131 4859367103342479411885197)
              ·
                refine ⟨1822262663753429779456949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4859367103342479411885197 1822262663753429779456949)
                ·
                  refine ⟨170837124726884041824089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1822262663753429779456949 170837124726884041824089)
                  ·
                    rfl

theorem cell23_2994337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 5].length) (baseStart_2994337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994337 prefixEnd_2994337 := by exact prefixLift 2994337
  have htrace : WordTrace (prefixWord ++ tailWord_2994337) baseStart_2994337 baseEnd_2994337 := by
    simpa [prefixWord, tailWord_2994337, baseEnd_2994337] using wordTrace_append hprefix tailTrace_2994337
  have hstable : (prefixWord ++ tailWord_2994337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994337).length < 2 ^ (prefixWord ++ tailWord_2994337).sum := by decide
  have hdescent : baseEnd_2994337 < baseStart_2994337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994373 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_2994373 : Nat := 118140960795 + 2994373 * 2 ^ 59
def prefixEnd_2994373 : Nat := 4983230072969 + 3 ^ 40 * 2994373 * 2
def baseEnd_2994373 : Nat := 1537552607845518235566635

theorem tailTrace_2994373 : CollatzResearch.WordTrace tailWord_2994373 prefixEnd_2994373 1537552607845518235566635 := by
  unfold tailWord_2994373
  simp only [CollatzResearch.WordTrace]
  refine ⟨109213755580905494039019773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72809170387270329359346515 109213755580905494039019773)
  ·
    refine ⟨40955158342839560264632415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109213755580905494039019773 40955158342839560264632415)
    ·
      refine ⟨61432737514259340396948623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40955158342839560264632415 61432737514259340396948623)
      ·
        refine ⟨92149106271389010595422935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61432737514259340396948623 92149106271389010595422935)
        ·
          refine ⟨138223659407083515893134403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92149106271389010595422935 138223659407083515893134403)
          ·
            refine ⟨207335489110625273839701605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138223659407083515893134403 207335489110625273839701605)
            ·
              refine ⟨38875404208242238844944051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207335489110625273839701605 38875404208242238844944051)
              ·
                refine ⟨58313106312363358267416077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38875404208242238844944051 58313106312363358267416077)
                ·
                  refine ⟨21867414867136259350281029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58313106312363358267416077 21867414867136259350281029)
                  ·
                    refine ⟨4100140287588048628177693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21867414867136259350281029 4100140287588048628177693)
                    ·
                      refine ⟨1537552607845518235566635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100140287588048628177693 1537552607845518235566635)
                      ·
                        rfl

theorem cell23_2994373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_2994373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994373 prefixEnd_2994373 := by exact prefixLift 2994373
  have htrace : WordTrace (prefixWord ++ tailWord_2994373) baseStart_2994373 baseEnd_2994373 := by
    simpa [prefixWord, tailWord_2994373, baseEnd_2994373] using wordTrace_append hprefix tailTrace_2994373
  have hstable : (prefixWord ++ tailWord_2994373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994373).length < 2 ^ (prefixWord ++ tailWord_2994373).sum := by decide
  have hdescent : baseEnd_2994373 < baseStart_2994373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994407 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2994407 : Nat := 118140960795 + 2994407 * 2 ^ 59
def prefixEnd_2994407 : Nat := 4983230072969 + 3 ^ 40 * 2994407 * 2
def baseEnd_2994407 : Nat := 1537570066187771102541479

theorem tailTrace_2994407 : CollatzResearch.WordTrace tailWord_2994407 prefixEnd_2994407 1537570066187771102541479 := by
  unfold tailWord_2994407
  simp only [CollatzResearch.WordTrace]
  refine ⟨109214995662782317845757475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72809997108521545230504983 109214995662782317845757475)
  ·
    refine ⟨163822493494173476768636213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109214995662782317845757475 163822493494173476768636213)
    ·
      refine ⟨15358358765078763447059645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163822493494173476768636213 15358358765078763447059645)
      ·
        refine ⟨5759384536904536292647367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15358358765078763447059645 5759384536904536292647367)
        ·
          refine ⟨8639076805356804438971051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759384536904536292647367 8639076805356804438971051)
          ·
            refine ⟨12958615208035206658456577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8639076805356804438971051 12958615208035206658456577)
            ·
              refine ⟨9718961406026404993842433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12958615208035206658456577 9718961406026404993842433)
              ·
                refine ⟨7289221054519803745381825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718961406026404993842433 7289221054519803745381825)
                ·
                  refine ⟨5466915790889852809036369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7289221054519803745381825 5466915790889852809036369)
                  ·
                    refine ⟨4100186843167389606777277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5466915790889852809036369 4100186843167389606777277)
                    ·
                      refine ⟨1537570066187771102541479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100186843167389606777277 1537570066187771102541479)
                      ·
                        rfl

theorem cell23_2994407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2994407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994407 prefixEnd_2994407 := by exact prefixLift 2994407
  have htrace : WordTrace (prefixWord ++ tailWord_2994407) baseStart_2994407 baseEnd_2994407 := by
    simpa [prefixWord, tailWord_2994407, baseEnd_2994407] using wordTrace_append hprefix tailTrace_2994407
  have hstable : (prefixWord ++ tailWord_2994407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994407).length < 2 ^ (prefixWord ++ tailWord_2994407).sum := by decide
  have hdescent : baseEnd_2994407 < baseStart_2994407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994410 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_2994410 : Nat := 118140960795 + 2994410 * 2 ^ 59
def prefixEnd_2994410 : Nat := 4983230072969 + 3 ^ 40 * 2994410 * 2
def baseEnd_2994410 : Nat := 170841289625526065644885

theorem tailTrace_2994410 : CollatzResearch.WordTrace tailWord_2994410 prefixEnd_2994410 170841289625526065644885 := by
  unfold tailWord_2994410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27303776270442862339529171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72810070054514299572077789 27303776270442862339529171)
  ·
    refine ⟨40955664405664293509293757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27303776270442862339529171 40955664405664293509293757)
    ·
      refine ⟨15358374152124110065985159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40955664405664293509293757 15358374152124110065985159)
      ·
        refine ⟨23037561228186165098977739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15358374152124110065985159 23037561228186165098977739)
        ·
          refine ⟨34556341842279247648466609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23037561228186165098977739 34556341842279247648466609)
          ·
            refine ⟨25917256381709435736349957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34556341842279247648466609 25917256381709435736349957)
            ·
              refine ⟨4859485571570519200565617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25917256381709435736349957 4859485571570519200565617)
              ·
                refine ⟨3644614178677889400424213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859485571570519200565617 3644614178677889400424213)
                ·
                  refine ⟨170841289625526065644885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3644614178677889400424213 170841289625526065644885)
                  ·
                    rfl

theorem cell23_2994410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_2994410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994410 prefixEnd_2994410 := by exact prefixLift 2994410
  have htrace : WordTrace (prefixWord ++ tailWord_2994410) baseStart_2994410 baseEnd_2994410 := by
    simpa [prefixWord, tailWord_2994410, baseEnd_2994410] using wordTrace_append hprefix tailTrace_2994410
  have hstable : (prefixWord ++ tailWord_2994410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994410).length < 2 ^ (prefixWord ++ tailWord_2994410).sum := by decide
  have hdescent : baseEnd_2994410 < baseStart_2994410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994433 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2994433 : Nat := 118140960795 + 2994433 * 2 ^ 59
def prefixEnd_2994433 : Nat := 4983230072969 + 3 ^ 40 * 2994433 * 2
def baseEnd_2994433 : Nat := 1537583416684788000816359

theorem tailTrace_2994433 : CollatzResearch.WordTrace tailWord_2994433 prefixEnd_2994433 1537583416684788000816359 := by
  unfold tailWord_2994433
  simp only [CollatzResearch.WordTrace]
  refine ⟨109215943960688124286203953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72810629307125416190802635 109215943960688124286203953)
  ·
    refine ⟨81911957970516093214652965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109215943960688124286203953 81911957970516093214652965)
    ·
      refine ⟨15358492119471767477747431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81911957970516093214652965 15358492119471767477747431)
      ·
        refine ⟨23037738179207651216621147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15358492119471767477747431 23037738179207651216621147)
        ·
          refine ⟨34556607268811476824931721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23037738179207651216621147 34556607268811476824931721)
          ·
            refine ⟨25917455451608607618698791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34556607268811476824931721 25917455451608607618698791)
            ·
              refine ⟨38876183177412911428048187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25917455451608607618698791 38876183177412911428048187)
              ·
                refine ⟨58314274766119367142072281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38876183177412911428048187 58314274766119367142072281)
                ·
                  refine ⟨43735706074589525356554211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58314274766119367142072281 43735706074589525356554211)
                  ·
                    refine ⟨65603559111884288034831317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43735706074589525356554211 65603559111884288034831317)
                    ·
                      refine ⟨1537583416684788000816359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65603559111884288034831317 1537583416684788000816359)
                      ·
                        rfl

theorem cell23_2994433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2994433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994433 prefixEnd_2994433 := by exact prefixLift 2994433
  have htrace : WordTrace (prefixWord ++ tailWord_2994433) baseStart_2994433 baseEnd_2994433 := by
    simpa [prefixWord, tailWord_2994433, baseEnd_2994433] using wordTrace_append hprefix tailTrace_2994433
  have hstable : (prefixWord ++ tailWord_2994433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994433).length < 2 ^ (prefixWord ++ tailWord_2994433).sum := by decide
  have hdescent : baseEnd_2994433 < baseStart_2994433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994440 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_2994440 : Nat := 118140960795 + 2994440 * 2 ^ 59
def prefixEnd_2994440 : Nat := 4983230072969 + 3 ^ 40 * 2994440 * 2
def baseEnd_2994440 : Nat := 512529003683123157809609

theorem tailTrace_2994440 : CollatzResearch.WordTrace tailWord_2994440 prefixEnd_2994440 512529003683123157809609 := by
  unfold tailWord_2994440
  simp only [CollatzResearch.WordTrace]
  refine ⟨54608099635831382240854387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72810799514441842987805849 54608099635831382240854387)
  ·
    refine ⟨81912149453747073361281581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54608099635831382240854387 81912149453747073361281581)
    ·
      refine ⟨30717056045155152510480593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81912149453747073361281581 30717056045155152510480593)
      ·
        refine ⟨23037792033866364382860445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30717056045155152510480593 23037792033866364382860445)
        ·
          refine ⟨8639172012699886643572667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23037792033866364382860445 8639172012699886643572667)
          ·
            refine ⟨12958758019049829965359001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8639172012699886643572667 12958758019049829965359001)
            ·
              refine ⟨9719068514287372474019251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12958758019049829965359001 9719068514287372474019251)
              ·
                refine ⟨14578602771431058711028877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9719068514287372474019251 14578602771431058711028877)
                ·
                  refine ⟨5466976039286647016635829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14578602771431058711028877 5466976039286647016635829)
                  ·
                    refine ⟨512529003683123157809609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5466976039286647016635829 512529003683123157809609)
                    ·
                      rfl

theorem cell23_2994440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_2994440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994440 prefixEnd_2994440 := by exact prefixLift 2994440
  have htrace : WordTrace (prefixWord ++ tailWord_2994440) baseStart_2994440 baseEnd_2994440 := by
    simpa [prefixWord, tailWord_2994440, baseEnd_2994440] using wordTrace_append hprefix tailTrace_2994440
  have hstable : (prefixWord ++ tailWord_2994440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994440).length < 2 ^ (prefixWord ++ tailWord_2994440).sum := by decide
  have hdescent : baseEnd_2994440 < baseStart_2994440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994480 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_2994480 : Nat := 118140960795 + 2994480 * 2 ^ 59
def prefixEnd_2994480 : Nat := 4983230072969 + 3 ^ 40 * 2994480 * 2
def baseEnd_2994480 : Nat := 1537607550275549316928643

theorem tailTrace_2994480 : CollatzResearch.WordTrace tailWord_2994480 prefixEnd_2994480 1537607550275549316928643 := by
  unfold tailWord_2994480
  simp only [CollatzResearch.WordTrace]
  refine ⟨54608829095758925656582447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72811772127678567542109929 54608829095758925656582447)
  ·
    refine ⟨81913243643638388484873671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54608829095758925656582447 81913243643638388484873671)
    ·
      refine ⟨122869865465457582727310507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81913243643638388484873671 122869865465457582727310507)
      ·
        refine ⟨184304798198186374090965761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122869865465457582727310507 184304798198186374090965761)
        ·
          refine ⟨138228598648639780568224321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184304798198186374090965761 138228598648639780568224321)
          ·
            refine ⟨103671448986479835426168241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138228598648639780568224321 103671448986479835426168241)
            ·
              refine ⟨77753586739859876569626181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103671448986479835426168241 77753586739859876569626181)
              ·
                refine ⟨14578797513723726856804909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77753586739859876569626181 14578797513723726856804909)
                ·
                  refine ⟨5467049067646397571301841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14578797513723726856804909 5467049067646397571301841)
                  ·
                    refine ⟨4100286800734798178476381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467049067646397571301841 4100286800734798178476381)
                    ·
                      refine ⟨1537607550275549316928643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100286800734798178476381 1537607550275549316928643)
                      ·
                        rfl

theorem cell23_2994480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_2994480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994480 prefixEnd_2994480 := by exact prefixLift 2994480
  have htrace : WordTrace (prefixWord ++ tailWord_2994480) baseStart_2994480 baseEnd_2994480 := by
    simpa [prefixWord, tailWord_2994480, baseEnd_2994480] using wordTrace_append hprefix tailTrace_2994480
  have hstable : (prefixWord ++ tailWord_2994480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994480).length < 2 ^ (prefixWord ++ tailWord_2994480).sum := by decide
  have hdescent : baseEnd_2994480 < baseStart_2994480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994483 : List Nat := [1, 1, 1, 2, 5, 1, 2, 10]
def baseStart_2994483 : Nat := 118140960795 + 2994483 * 2 ^ 59
def prefixEnd_2994483 : Nat := 4983230072969 + 3 ^ 40 * 2994483 * 2
def baseEnd_2994483 : Nat := 56948484841389363155227

theorem tailTrace_2994483 : CollatzResearch.WordTrace tailWord_2994483 prefixEnd_2994483 56948484841389363155227 := by
  unfold tailWord_2994483
  simp only [CollatzResearch.WordTrace]
  refine ⟨109217767610506982825524103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72811845073671321883682735 109217767610506982825524103)
  ·
    refine ⟨163826651415760474238286155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109217767610506982825524103 163826651415760474238286155)
    ·
      refine ⟨245739977123640711357429233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163826651415760474238286155 245739977123640711357429233)
      ·
        refine ⟨184304982842730533518071925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245739977123640711357429233 184304982842730533518071925)
        ·
          refine ⟨17278592141505987517319243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184304982842730533518071925 17278592141505987517319243)
          ·
            refine ⟨25917888212258981275978865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17278592141505987517319243 25917888212258981275978865)
            ·
              refine ⟨19438416159194235956984149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25917888212258981275978865 19438416159194235956984149)
              ·
                refine ⟨56948484841389363155227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19438416159194235956984149 56948484841389363155227)
                ·
                  rfl

theorem cell23_2994483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 10].length) (baseStart_2994483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994483 prefixEnd_2994483 := by exact prefixLift 2994483
  have htrace : WordTrace (prefixWord ++ tailWord_2994483) baseStart_2994483 baseEnd_2994483 := by
    simpa [prefixWord, tailWord_2994483, baseEnd_2994483] using wordTrace_append hprefix tailTrace_2994483
  have hstable : (prefixWord ++ tailWord_2994483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994483).length < 2 ^ (prefixWord ++ tailWord_2994483).sum := by decide
  have hdescent : baseEnd_2994483 < baseStart_2994483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994490 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_2994490 : Nat := 118140960795 + 2994490 * 2 ^ 59
def prefixEnd_2994490 : Nat := 4983230072969 + 3 ^ 40 * 2994490 * 2
def baseEnd_2994490 : Nat := 1537612685082094277803597

theorem tailTrace_2994490 : CollatzResearch.WordTrace tailWord_2994490 prefixEnd_2994490 1537612685082094277803597 := by
  unfold tailWord_2994490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27304505730370405755257231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72812015280987748680685949 27304505730370405755257231)
  ·
    refine ⟨40956758595555608632885847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27304505730370405755257231 40956758595555608632885847)
    ·
      refine ⟨61435137893333412949328771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40956758595555608632885847 61435137893333412949328771)
      ·
        refine ⟨92152706840000119423993157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61435137893333412949328771 92152706840000119423993157)
        ·
          refine ⟨17278632532500022391998717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92152706840000119423993157 17278632532500022391998717)
          ·
            refine ⟨6479487199687508396999519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17278632532500022391998717 6479487199687508396999519)
            ·
              refine ⟨9719230799531262595499279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479487199687508396999519 9719230799531262595499279)
              ·
                refine ⟨14578846199296893893248919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9719230799531262595499279 14578846199296893893248919)
                ·
                  refine ⟨21868269298945340839873379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14578846199296893893248919 21868269298945340839873379)
                  ·
                    refine ⟨32802403948418011259810069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21868269298945340839873379 32802403948418011259810069)
                    ·
                      refine ⟨1537612685082094277803597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32802403948418011259810069 1537612685082094277803597)
                      ·
                        rfl

theorem cell23_2994490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_2994490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994490 prefixEnd_2994490 := by exact prefixLift 2994490
  have htrace : WordTrace (prefixWord ++ tailWord_2994490) baseStart_2994490 baseEnd_2994490 := by
    simpa [prefixWord, tailWord_2994490, baseEnd_2994490] using wordTrace_append hprefix tailTrace_2994490
  have hstable : (prefixWord ++ tailWord_2994490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994490).length < 2 ^ (prefixWord ++ tailWord_2994490).sum := by decide
  have hdescent : baseEnd_2994490 < baseStart_2994490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994494 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2994494 : Nat := 118140960795 + 2994494 * 2 ^ 59
def prefixEnd_2994494 : Nat := 4983230072969 + 3 ^ 40 * 2994494 * 2
def baseEnd_2994494 : Nat := 1537614739004712262153579

theorem tailTrace_2994494 : CollatzResearch.WordTrace tailWord_2994494 prefixEnd_2994494 1537614739004712262153579 := by
  unfold tailWord_2994494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13652271101683391463021817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72812112542311421136116357 13652271101683391463021817)
  ·
    refine ⟨10239203326262543597266363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13652271101683391463021817 10239203326262543597266363)
    ·
      refine ⟨15358804989393815395899545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10239203326262543597266363 15358804989393815395899545)
      ·
        refine ⟨11519103742045361546924659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15358804989393815395899545 11519103742045361546924659)
        ·
          refine ⟨17278655613068042320386989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11519103742045361546924659 17278655613068042320386989)
          ·
            refine ⟨6479495854900515870145121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17278655613068042320386989 6479495854900515870145121)
            ·
              refine ⟨4859621891175386902608841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6479495854900515870145121 4859621891175386902608841)
              ·
                refine ⟨3644716418381540176956631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859621891175386902608841 3644716418381540176956631)
                ·
                  refine ⟨5467074627572310265434947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644716418381540176956631 5467074627572310265434947)
                  ·
                    refine ⟨8200611941358465398152421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5467074627572310265434947 8200611941358465398152421)
                    ·
                      refine ⟨1537614739004712262153579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8200611941358465398152421 1537614739004712262153579)
                      ·
                        rfl

theorem cell23_2994494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2994494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994494 prefixEnd_2994494 := by exact prefixLift 2994494
  have htrace : WordTrace (prefixWord ++ tailWord_2994494) baseStart_2994494 baseEnd_2994494 := by
    simpa [prefixWord, tailWord_2994494, baseEnd_2994494] using wordTrace_append hprefix tailTrace_2994494
  have hstable : (prefixWord ++ tailWord_2994494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994494).length < 2 ^ (prefixWord ++ tailWord_2994494).sum := by decide
  have hdescent : baseEnd_2994494 < baseStart_2994494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994517 : List Nat := [1, 3, 2, 2, 5, 1, 9]
def baseStart_2994517 : Nat := 118140960795 + 2994517 * 2 ^ 59
def prefixEnd_2994517 : Nat := 4983230072969 + 3 ^ 40 * 2994517 * 2
def baseEnd_2994517 : Nat := 18983043815552662619333

theorem tailTrace_2994517 : CollatzResearch.WordTrace tailWord_2994517 prefixEnd_2994517 18983043815552662619333 := by
  unfold tailWord_2994517
  simp only [CollatzResearch.WordTrace]
  refine ⟨109219007692383806632261805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72812671794922537754841203 109219007692383806632261805)
  ·
    refine ⟨40957127884643927487098177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109219007692383806632261805 40957127884643927487098177)
    ·
      refine ⟨30717845913482945615323633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40957127884643927487098177 30717845913482945615323633)
      ·
        refine ⟨23038384435112209211492725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30717845913482945615323633 23038384435112209211492725)
        ·
          refine ⟨2159848540791769613577443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23038384435112209211492725 2159848540791769613577443)
          ·
            refine ⟨3239772811187654420366165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159848540791769613577443 3239772811187654420366165)
            ·
              refine ⟨18983043815552662619333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3239772811187654420366165 18983043815552662619333)
              ·
                rfl

theorem cell23_2994517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 9].length) (baseStart_2994517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994517 prefixEnd_2994517 := by exact prefixLift 2994517
  have htrace : WordTrace (prefixWord ++ tailWord_2994517) baseStart_2994517 baseEnd_2994517 := by
    simpa [prefixWord, tailWord_2994517, baseEnd_2994517] using wordTrace_append hprefix tailTrace_2994517
  have hstable : (prefixWord ++ tailWord_2994517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994517).length < 2 ^ (prefixWord ++ tailWord_2994517).sum := by decide
  have hdescent : baseEnd_2994517 < baseStart_2994517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994523 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_2994523 : Nat := 118140960795 + 2994523 * 2 ^ 59
def prefixEnd_2994523 : Nat := 4983230072969 + 3 ^ 40 * 2994523 * 2
def baseEnd_2994523 : Nat := 1537629629943692648690945

theorem tailTrace_2994523 : CollatzResearch.WordTrace tailWord_2994523 prefixEnd_2994523 1537629629943692648690945 := by
  unfold tailWord_2994523
  simp only [CollatzResearch.WordTrace]
  refine ⟨109219226530362069656980223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72812817686908046437986815 109219226530362069656980223)
  ·
    refine ⟨163828839795543104485470335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109219226530362069656980223 163828839795543104485470335)
    ·
      refine ⟨245743259693314656728205503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163828839795543104485470335 245743259693314656728205503)
      ·
        refine ⟨368614889539971985092308255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245743259693314656728205503 368614889539971985092308255)
        ·
          refine ⟨552922334309957977638462383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368614889539971985092308255 552922334309957977638462383)
          ·
            refine ⟨829383501464936966457693575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552922334309957977638462383 829383501464936966457693575)
            ·
              refine ⟨1244075252197405449686540363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829383501464936966457693575 1244075252197405449686540363)
              ·
                refine ⟨1866112878296108174529810545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244075252197405449686540363 1866112878296108174529810545)
                ·
                  refine ⟨1399584658722081130897357909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866112878296108174529810545 1399584658722081130897357909)
                  ·
                    refine ⟨16401382719399388252703413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1399584658722081130897357909 16401382719399388252703413)
                    ·
                      refine ⟨1537629629943692648690945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16401382719399388252703413 1537629629943692648690945)
                      ·
                        rfl

theorem cell23_2994523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_2994523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994523 prefixEnd_2994523 := by exact prefixLift 2994523
  have htrace : WordTrace (prefixWord ++ tailWord_2994523) baseStart_2994523 baseEnd_2994523 := by
    simpa [prefixWord, tailWord_2994523, baseEnd_2994523] using wordTrace_append hprefix tailTrace_2994523
  have hstable : (prefixWord ++ tailWord_2994523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994523).length < 2 ^ (prefixWord ++ tailWord_2994523).sum := by decide
  have hdescent : baseEnd_2994523 < baseStart_2994523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994527 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 3]
def baseStart_2994527 : Nat := 118140960795 + 2994527 * 2 ^ 59
def prefixEnd_2994527 : Nat := 4983230072969 + 3 ^ 40 * 2994527 * 2
def baseEnd_2994527 : Nat := 1537631683866310633040927

theorem tailTrace_2994527 : CollatzResearch.WordTrace tailWord_2994527 prefixEnd_2994527 1537631683866310633040927 := by
  unfold tailWord_2994527
  simp only [CollatzResearch.WordTrace]
  refine ⟨109219372422347578340125835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72812914948231718893417223 109219372422347578340125835)
  ·
    refine ⟨163829058633521367510188753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109219372422347578340125835 163829058633521367510188753)
    ·
      refine ⟨122871793975141025632641565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163829058633521367510188753 122871793975141025632641565)
      ·
        refine ⟨46076922740677884612240587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122871793975141025632641565 46076922740677884612240587)
        ·
          refine ⟨69115384111016826918360881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46076922740677884612240587 69115384111016826918360881)
          ·
            refine ⟨51836538083262620188770661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69115384111016826918360881 51836538083262620188770661)
            ·
              refine ⟨9719350890611741285394499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51836538083262620188770661 9719350890611741285394499)
              ·
                refine ⟨14579026335917611928091749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9719350890611741285394499 14579026335917611928091749)
                ·
                  refine ⟨2733567437984552236517203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14579026335917611928091749 2733567437984552236517203)
                  ·
                    refine ⟨4100351156976828354775805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733567437984552236517203 4100351156976828354775805)
                    ·
                      refine ⟨1537631683866310633040927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100351156976828354775805 1537631683866310633040927)
                      ·
                        rfl

theorem cell23_2994527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_2994527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994527 prefixEnd_2994527 := by exact prefixLift 2994527
  have htrace : WordTrace (prefixWord ++ tailWord_2994527) baseStart_2994527 baseEnd_2994527 := by
    simpa [prefixWord, tailWord_2994527, baseEnd_2994527] using wordTrace_append hprefix tailTrace_2994527
  have hstable : (prefixWord ++ tailWord_2994527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994527).length < 2 ^ (prefixWord ++ tailWord_2994527).sum := by decide
  have hdescent : baseEnd_2994527 < baseStart_2994527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994528 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 3, 2, 2]
def baseStart_2994528 : Nat := 118140960795 + 2994528 * 2 ^ 59
def prefixEnd_2994528 : Nat := 4983230072969 + 3 ^ 40 * 2994528 * 2
def baseEnd_2994528 : Nat := 1537632197346965129128423

theorem tailTrace_2994528 : CollatzResearch.WordTrace tailWord_2994528 prefixEnd_2994528 1537632197346965129128423 := by
  unfold tailWord_2994528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609704447671977755456119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72812939263562637007274825 54609704447671977755456119)
  ·
    refine ⟨81914556671507966633184179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54609704447671977755456119 81914556671507966633184179)
    ·
      refine ⟨122871835007261949949776269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81914556671507966633184179 122871835007261949949776269)
      ·
        refine ⟨46076938127723231231166101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122871835007261949949776269 46076938127723231231166101)
        ·
          refine ⟨2159856474737026463960911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46076938127723231231166101 2159856474737026463960911)
          ·
            refine ⟨3239784712105539695941367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159856474737026463960911 3239784712105539695941367)
            ·
              refine ⟨4859677068158309543912051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239784712105539695941367 4859677068158309543912051)
              ·
                refine ⟨7289515602237464315868077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859677068158309543912051 7289515602237464315868077)
                ·
                  refine ⟨2733568350839049118450529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7289515602237464315868077 2733568350839049118450529)
                  ·
                    refine ⟨2050176263129286838837897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2733568350839049118450529 2050176263129286838837897)
                    ·
                      refine ⟨1537632197346965129128423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050176263129286838837897 1537632197346965129128423)
                      ·
                        rfl

theorem cell23_2994528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_2994528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994528 prefixEnd_2994528 := by exact prefixLift 2994528
  have htrace : WordTrace (prefixWord ++ tailWord_2994528) baseStart_2994528 baseEnd_2994528 := by
    simpa [prefixWord, tailWord_2994528, baseEnd_2994528] using wordTrace_append hprefix tailTrace_2994528
  have hstable : (prefixWord ++ tailWord_2994528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994528).length < 2 ^ (prefixWord ++ tailWord_2994528).sum := by decide
  have hdescent : baseEnd_2994528 < baseStart_2994528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994537 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 3, 3, 2]
def baseStart_2994537 : Nat := 118140960795 + 2994537 * 2 ^ 59
def prefixEnd_2994537 : Nat := 4983230072969 + 3 ^ 40 * 2994537 * 2
def baseEnd_2994537 : Nat := 1537636818672855593915881

theorem tailTrace_2994537 : CollatzResearch.WordTrace tailWord_2994537 prefixEnd_2994537 1537636818672855593915881 := by
  unfold tailWord_2994537
  simp only [CollatzResearch.WordTrace]
  refine ⟨109219737152311350047989865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72813158101540900031993243 109219737152311350047989865)
  ·
    refine ⟨81914802864233512535992399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109219737152311350047989865 81914802864233512535992399)
    ·
      refine ⟨122872204296350268803988599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81914802864233512535992399 122872204296350268803988599)
      ·
        refine ⟨184308306444525403205982899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122872204296350268803988599 184308306444525403205982899)
        ·
          refine ⟨276462459666788104808974349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184308306444525403205982899 276462459666788104808974349)
          ·
            refine ⟨103673422375045539303365381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276462459666788104808974349 103673422375045539303365381)
            ·
              refine ⟨19438766695321038619381009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103673422375045539303365381 19438766695321038619381009)
              ·
                refine ⟨14579075021490778964535757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19438766695321038619381009 14579075021490778964535757)
                ·
                  refine ⟨5467153133059042111700909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14579075021490778964535757 5467153133059042111700909)
                  ·
                    refine ⟨2050182424897140791887841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5467153133059042111700909 2050182424897140791887841)
                    ·
                      refine ⟨1537636818672855593915881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050182424897140791887841 1537636818672855593915881)
                      ·
                        rfl

theorem cell23_2994537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 3, 2].length) (baseStart_2994537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994537 prefixEnd_2994537 := by exact prefixLift 2994537
  have htrace : WordTrace (prefixWord ++ tailWord_2994537) baseStart_2994537 baseEnd_2994537 := by
    simpa [prefixWord, tailWord_2994537, baseEnd_2994537] using wordTrace_append hprefix tailTrace_2994537
  have hstable : (prefixWord ++ tailWord_2994537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994537).length < 2 ^ (prefixWord ++ tailWord_2994537).sum := by decide
  have hdescent : baseEnd_2994537 < baseStart_2994537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994544 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 2, 1, 3]
def baseStart_2994544 : Nat := 118140960795 + 2994544 * 2 ^ 59
def prefixEnd_2994544 : Nat := 4983230072969 + 3 ^ 40 * 2994544 * 2
def baseEnd_2994544 : Nat := 1537640413037437066528349

theorem tailTrace_2994544 : CollatzResearch.WordTrace tailWord_2994544 prefixEnd_2994544 1537640413037437066528349 := by
  unfold tailWord_2994544
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609996231642995121747343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72813328308857326828996457 54609996231642995121747343)
  ·
    refine ⟨81914994347464492682621015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54609996231642995121747343 81914994347464492682621015)
    ·
      refine ⟨122872491521196739023931523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81914994347464492682621015 122872491521196739023931523)
      ·
        refine ⟨184308737281795108535897285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122872491521196739023931523 184308737281795108535897285)
        ·
          refine ⟨34557888240336582850480741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184308737281795108535897285 34557888240336582850480741)
          ·
            refine ⟨6479604045063109284465139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34557888240336582850480741 6479604045063109284465139)
            ·
              refine ⟨9719406067594663926697709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479604045063109284465139 9719406067594663926697709)
              ·
                refine ⟨3644777275347998972511641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9719406067594663926697709 3644777275347998972511641)
                ·
                  refine ⟨2733582956510999229383731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644777275347998972511641 2733582956510999229383731)
                  ·
                    refine ⟨4100374434766498844075597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733582956510999229383731 4100374434766498844075597)
                    ·
                      refine ⟨1537640413037437066528349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100374434766498844075597 1537640413037437066528349)
                      ·
                        rfl

theorem cell23_2994544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_2994544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994544 prefixEnd_2994544 := by exact prefixLift 2994544
  have htrace : WordTrace (prefixWord ++ tailWord_2994544) baseStart_2994544 baseEnd_2994544 := by
    simpa [prefixWord, tailWord_2994544, baseEnd_2994544] using wordTrace_append hprefix tailTrace_2994544
  have hstable : (prefixWord ++ tailWord_2994544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994544).length < 2 ^ (prefixWord ++ tailWord_2994544).sum := by decide
  have hdescent : baseEnd_2994544 < baseStart_2994544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994571 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 1, 3, 2]
def baseStart_2994571 : Nat := 118140960795 + 2994571 * 2 ^ 59
def prefixEnd_2994571 : Nat := 4983230072969 + 3 ^ 40 * 2994571 * 2
def baseEnd_2994571 : Nat := 1537654277015108460890725

theorem tailTrace_2994571 : CollatzResearch.WordTrace tailWord_2994571 prefixEnd_2994571 1537654277015108460890725 := by
  unfold tailWord_2994571
  simp only [CollatzResearch.WordTrace]
  refine ⟨109220977234188173854727567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72813984822792115903151711 109220977234188173854727567)
  ·
    refine ⟨163831465851282260782091351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109220977234188173854727567 163831465851282260782091351)
    ·
      refine ⟨245747198776923391173137027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163831465851282260782091351 245747198776923391173137027)
      ·
        refine ⟨368620798165385086759705541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245747198776923391173137027 368620798165385086759705541)
        ·
          refine ⟨69116399656009703767444789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368620798165385086759705541 69116399656009703767444789)
          ·
            refine ⟨6479662467750909728197949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69116399656009703767444789 6479662467750909728197949)
            ·
              refine ⟨2429873425406591148074231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6479662467750909728197949 2429873425406591148074231)
              ·
                refine ⟨3644810138109886722111347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429873425406591148074231 3644810138109886722111347)
                ·
                  refine ⟨5467215207164830083167021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644810138109886722111347 5467215207164830083167021)
                  ·
                    refine ⟨2050205702686811281187633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5467215207164830083167021 2050205702686811281187633)
                    ·
                      refine ⟨1537654277015108460890725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050205702686811281187633 1537654277015108460890725)
                      ·
                        rfl

theorem cell23_2994571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 3, 2].length) (baseStart_2994571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994571 prefixEnd_2994571 := by exact prefixLift 2994571
  have htrace : WordTrace (prefixWord ++ tailWord_2994571) baseStart_2994571 baseEnd_2994571 := by
    simpa [prefixWord, tailWord_2994571, baseEnd_2994571] using wordTrace_append hprefix tailTrace_2994571
  have hstable : (prefixWord ++ tailWord_2994571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994571).length < 2 ^ (prefixWord ++ tailWord_2994571).sum := by decide
  have hdescent : baseEnd_2994571 < baseStart_2994571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994640 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_2994640 : Nat := 118140960795 + 2994640 * 2 ^ 59
def prefixEnd_2994640 : Nat := 4983230072969 + 3 ^ 40 * 2994640 * 2
def baseEnd_2994640 : Nat := 1537689707180268690927907

theorem tailTrace_2994640 : CollatzResearch.WordTrace tailWord_2994640 prefixEnd_2994640 1537689707180268690927907 := by
  unfold tailWord_2994640
  simp only [CollatzResearch.WordTrace]
  refine ⟨54611746935469099319494687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72815662580625465759326249 54611746935469099319494687)
  ·
    refine ⟨81917620403203648979242031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54611746935469099319494687 81917620403203648979242031)
    ·
      refine ⟨122876430604805473468863047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81917620403203648979242031 122876430604805473468863047)
      ·
        refine ⟨184314645907208210203294571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122876430604805473468863047 184314645907208210203294571)
        ·
          refine ⟨276471968860812315304941857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184314645907208210203294571 276471968860812315304941857)
          ·
            refine ⟨207353976645609236478706393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276471968860812315304941857 207353976645609236478706393)
            ·
              refine ⟨155515482484206927359029795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207353976645609236478706393 155515482484206927359029795)
              ·
                refine ⟨233273223726310391038544693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155515482484206927359029795 233273223726310391038544693)
                ·
                  refine ⟨21869364724341599159863565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233273223726310391038544693 21869364724341599159863565)
                  ·
                    refine ⟨8201011771628099684948837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21869364724341599159863565 8201011771628099684948837)
                    ·
                      refine ⟨1537689707180268690927907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8201011771628099684948837 1537689707180268690927907)
                      ·
                        rfl

theorem cell23_2994640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_2994640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994640 prefixEnd_2994640 := by exact prefixLift 2994640
  have htrace : WordTrace (prefixWord ++ tailWord_2994640) baseStart_2994640 baseEnd_2994640 := by
    simpa [prefixWord, tailWord_2994640, baseEnd_2994640] using wordTrace_append hprefix tailTrace_2994640
  have hstable : (prefixWord ++ tailWord_2994640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994640).length < 2 ^ (prefixWord ++ tailWord_2994640).sum := by decide
  have hdescent : baseEnd_2994640 < baseStart_2994640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994667 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 3, 4]
def baseStart_2994667 : Nat := 118140960795 + 2994667 * 2 ^ 59
def prefixEnd_2994667 : Nat := 4983230072969 + 3 ^ 40 * 2994667 * 2
def baseEnd_2994667 : Nat := 512567857052646695096761

theorem tailTrace_2994667 : CollatzResearch.WordTrace tailWord_2994667 prefixEnd_2994667 512567857052646695096761 := by
  unfold tailWord_2994667
  simp only [CollatzResearch.WordTrace]
  refine ⟨109224478641840382250222255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72816319094560254833481503 109224478641840382250222255)
  ·
    refine ⟨163836717962760573375333383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109224478641840382250222255 163836717962760573375333383)
    ·
      refine ⟨245755076944140860063000075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163836717962760573375333383 245755076944140860063000075)
      ·
        refine ⟨368632615416211290094500113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245755076944140860063000075 368632615416211290094500113)
        ·
          refine ⟨276474461562158467570875085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368632615416211290094500113 276474461562158467570875085)
          ·
            refine ⟨103677923085809425339078157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276474461562158467570875085 103677923085809425339078157)
            ·
              refine ⟨38879221157178534502154309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103677923085809425339078157 38879221157178534502154309)
              ·
                refine ⟨7289853966970975219153933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38879221157178534502154309 7289853966970975219153933)
                ·
                  refine ⟨2733695237614115707182725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7289853966970975219153933 2733695237614115707182725)
                  ·
                    refine ⟨512567857052646695096761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2733695237614115707182725 512567857052646695096761)
                    ·
                      rfl

theorem cell23_2994667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 4].length) (baseStart_2994667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994667 prefixEnd_2994667 := by exact prefixLift 2994667
  have htrace : WordTrace (prefixWord ++ tailWord_2994667) baseStart_2994667 baseEnd_2994667 := by
    simpa [prefixWord, tailWord_2994667, baseEnd_2994667] using wordTrace_append hprefix tailTrace_2994667
  have hstable : (prefixWord ++ tailWord_2994667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994667).length < 2 ^ (prefixWord ++ tailWord_2994667).sum := by decide
  have hdescent : baseEnd_2994667 < baseStart_2994667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994680 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 10]
def baseStart_2994680 : Nat := 118140960795 + 2994680 * 2 ^ 59
def prefixEnd_2994680 : Nat := 4983230072969 + 3 ^ 40 * 2994680 * 2
def baseEnd_2994680 : Nat := 170856694045160948269747

theorem tailTrace_2994680 : CollatzResearch.WordTrace tailWord_2994680 prefixEnd_2994680 170856694045160948269747 := by
  unfold tailWord_2994680
  simp only [CollatzResearch.WordTrace]
  refine ⟨54612476395396642735222747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72816635193862190313630329 54612476395396642735222747)
  ·
    refine ⟨81918714593094964102834121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54612476395396642735222747 81918714593094964102834121)
    ·
      refine ⟨61439035944821223077125591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81918714593094964102834121 61439035944821223077125591)
      ·
        refine ⟨92158553917231834615688387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61439035944821223077125591 92158553917231834615688387)
        ·
          refine ⟨138237830875847751923532581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92158553917231834615688387 138237830875847751923532581)
          ·
            refine ⟨25919593289221453485662359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138237830875847751923532581 25919593289221453485662359)
            ·
              refine ⟨38879389933832180228493539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25919593289221453485662359 38879389933832180228493539)
              ·
                refine ⟨58319084900748270342740309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38879389933832180228493539 58319084900748270342740309)
                ·
                  refine ⟨170856694045160948269747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58319084900748270342740309 170856694045160948269747)
                  ·
                    rfl

theorem cell23_2994680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_2994680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994680 prefixEnd_2994680 := by exact prefixLift 2994680
  have htrace : WordTrace (prefixWord ++ tailWord_2994680) baseStart_2994680 baseEnd_2994680 := by
    simpa [prefixWord, tailWord_2994680, baseEnd_2994680] using wordTrace_append hprefix tailTrace_2994680
  have hstable : (prefixWord ++ tailWord_2994680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994680).length < 2 ^ (prefixWord ++ tailWord_2994680).sum := by decide
  have hdescent : baseEnd_2994680 < baseStart_2994680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994714 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_2994714 : Nat := 118140960795 + 2994714 * 2 ^ 59
def prefixEnd_2994714 : Nat := 4983230072969 + 3 ^ 40 * 2994714 * 2
def baseEnd_2994714 : Nat := 170858633860966822378063

theorem tailTrace_2994714 : CollatzResearch.WordTrace tailWord_2994714 prefixEnd_2994714 170858633860966822378063 := by
  unfold tailWord_2994714
  simp only [CollatzResearch.WordTrace]
  refine ⟨27306548218167527319295799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72817461915113406184788797 27306548218167527319295799)
  ·
    refine ⟨40959822327251290978943699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27306548218167527319295799 40959822327251290978943699)
    ·
      refine ⟨61439733490876936468415549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40959822327251290978943699 61439733490876936468415549)
      ·
        refine ⟨23039900059078851175655831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61439733490876936468415549 23039900059078851175655831)
        ·
          refine ⟨34559850088618276763483747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23039900059078851175655831 34559850088618276763483747)
          ·
            refine ⟨51839775132927415145225621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34559850088618276763483747 51839775132927415145225621)
            ·
              refine ⟨2429989459355972584932451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51839775132927415145225621 2429989459355972584932451)
              ·
                refine ⟨3644984189033958877398677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429989459355972584932451 3644984189033958877398677)
                ·
                  refine ⟨170858633860966822378063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3644984189033958877398677 170858633860966822378063)
                  ·
                    rfl

theorem cell23_2994714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_2994714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994714 prefixEnd_2994714 := by exact prefixLift 2994714
  have htrace : WordTrace (prefixWord ++ tailWord_2994714) baseStart_2994714 baseEnd_2994714 := by
    simpa [prefixWord, tailWord_2994714, baseEnd_2994714] using wordTrace_append hprefix tailTrace_2994714
  have hstable : (prefixWord ++ tailWord_2994714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994714).length < 2 ^ (prefixWord ++ tailWord_2994714).sum := by decide
  have hdescent : baseEnd_2994714 < baseStart_2994714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994767 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_2994767 : Nat := 118140960795 + 2994767 * 2 ^ 59
def prefixEnd_2994767 : Nat := 4983230072969 + 3 ^ 40 * 2994767 * 2
def baseEnd_2994767 : Nat := 1537754919223389694039823

theorem tailTrace_2994767 : CollatzResearch.WordTrace tailWord_2994767 prefixEnd_2994767 1537754919223389694039823 := by
  unfold tailWord_2994767
  simp only [CollatzResearch.WordTrace]
  refine ⟨109228125941478099328862555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72818750627652066219241703 109228125941478099328862555)
  ·
    refine ⟨163842188912217148993293833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109228125941478099328862555 163842188912217148993293833)
    ·
      refine ⟨122881641684162861744970375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163842188912217148993293833 122881641684162861744970375)
      ·
        refine ⟨184322462526244292617455563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122881641684162861744970375 184322462526244292617455563)
        ·
          refine ⟨276483693789366438926183345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184322462526244292617455563 276483693789366438926183345)
          ·
            refine ⟨207362770342024829194637509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276483693789366438926183345 207362770342024829194637509)
            ·
              refine ⟨38880519439129655473994533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207362770342024829194637509 38880519439129655473994533)
              ·
                refine ⟨7290097394836810401373975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38880519439129655473994533 7290097394836810401373975)
                ·
                  refine ⟨10935146092255215602060963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290097394836810401373975 10935146092255215602060963)
                  ·
                    refine ⟨16402719138382823403091445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10935146092255215602060963 16402719138382823403091445)
                    ·
                      refine ⟨1537754919223389694039823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16402719138382823403091445 1537754919223389694039823)
                      ·
                        rfl

theorem cell23_2994767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_2994767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994767 prefixEnd_2994767 := by exact prefixLift 2994767
  have htrace : WordTrace (prefixWord ++ tailWord_2994767) baseStart_2994767 baseEnd_2994767 := by
    simpa [prefixWord, tailWord_2994767, baseEnd_2994767] using wordTrace_append hprefix tailTrace_2994767
  have hstable : (prefixWord ++ tailWord_2994767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994767).length < 2 ^ (prefixWord ++ tailWord_2994767).sum := by decide
  have hdescent : baseEnd_2994767 < baseStart_2994767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994784 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_2994784 : Nat := 118140960795 + 2994784 * 2 ^ 59
def prefixEnd_2994784 : Nat := 4983230072969 + 3 ^ 40 * 2994784 * 2
def baseEnd_2994784 : Nat := 1537763648394516127527245

theorem tailTrace_2994784 : CollatzResearch.WordTrace tailWord_2994784 prefixEnd_2994784 1537763648394516127527245 := by
  unfold tailWord_2994784
  simp only [CollatzResearch.WordTrace]
  refine ⟨54614372991208255616115703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72819163988277674154820937 54614372991208255616115703)
  ·
    refine ⟨81921559486812383424173555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54614372991208255616115703 81921559486812383424173555)
    ·
      refine ⟨122882339230218575136260333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81921559486812383424173555 122882339230218575136260333)
      ·
        refine ⟨46080877211331965676097625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122882339230218575136260333 46080877211331965676097625)
        ·
          refine ⟨34560657908498974257073219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46080877211331965676097625 34560657908498974257073219)
          ·
            refine ⟨51840986862748461385609829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34560657908498974257073219 51840986862748461385609829)
            ·
              refine ⟨9720185036765336509801843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51840986862748461385609829 9720185036765336509801843)
              ·
                refine ⟨14580277555148004764702765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9720185036765336509801843 14580277555148004764702765)
                ·
                  refine ⟨5467604083180501786763537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14580277555148004764702765 5467604083180501786763537)
                  ·
                    refine ⟨4100703062385376340072653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467604083180501786763537 4100703062385376340072653)
                    ·
                      refine ⟨1537763648394516127527245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100703062385376340072653 1537763648394516127527245)
                      ·
                        rfl

theorem cell23_2994784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_2994784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994784 prefixEnd_2994784 := by exact prefixLift 2994784
  have htrace : WordTrace (prefixWord ++ tailWord_2994784) baseStart_2994784 baseEnd_2994784 := by
    simpa [prefixWord, tailWord_2994784, baseEnd_2994784] using wordTrace_append hprefix tailTrace_2994784
  have hstable : (prefixWord ++ tailWord_2994784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994784).length < 2 ^ (prefixWord ++ tailWord_2994784).sum := by decide
  have hdescent : baseEnd_2994784 < baseStart_2994784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994794 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2994794 : Nat := 118140960795 + 2994794 * 2 ^ 59
def prefixEnd_2994794 : Nat := 4983230072969 + 3 ^ 40 * 2994794 * 2
def baseEnd_2994794 : Nat := 1537768783201061088402199

theorem tailTrace_2994794 : CollatzResearch.WordTrace tailWord_2994794 prefixEnd_2994794 1537768783201061088402199 := by
  unfold tailWord_2994794
  simp only [CollatzResearch.WordTrace]
  refine ⟨27307277678095070735023859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72819407141586855293396957 27307277678095070735023859)
  ·
    refine ⟨40960916517142606102535789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27307277678095070735023859 40960916517142606102535789)
    ·
      refine ⟨15360343693928477288450921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40960916517142606102535789 15360343693928477288450921)
      ·
        refine ⟨11520257770446357966338191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15360343693928477288450921 11520257770446357966338191)
        ·
          refine ⟨17280386655669536949507287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520257770446357966338191 17280386655669536949507287)
          ·
            refine ⟨25920579983504305424260931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17280386655669536949507287 25920579983504305424260931)
            ·
              refine ⟨38880869975256458136391397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25920579983504305424260931 38880869975256458136391397)
              ·
                refine ⟨7290163120360585900573387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38880869975256458136391397 7290163120360585900573387)
                ·
                  refine ⟨10935244680540878850860081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7290163120360585900573387 10935244680540878850860081)
                  ·
                    refine ⟨8201433510405659138145061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10935244680540878850860081 8201433510405659138145061)
                    ·
                      refine ⟨1537768783201061088402199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8201433510405659138145061 1537768783201061088402199)
                      ·
                        rfl

theorem cell23_2994794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2994794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994794 prefixEnd_2994794 := by exact prefixLift 2994794
  have htrace : WordTrace (prefixWord ++ tailWord_2994794) baseStart_2994794 baseEnd_2994794 := by
    simpa [prefixWord, tailWord_2994794, baseEnd_2994794] using wordTrace_append hprefix tailTrace_2994794
  have hstable : (prefixWord ++ tailWord_2994794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994794).length < 2 ^ (prefixWord ++ tailWord_2994794).sum := by decide
  have hdescent : baseEnd_2994794 < baseStart_2994794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994798 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2994798 : Nat := 118140960795 + 2994798 * 2 ^ 59
def prefixEnd_2994798 : Nat := 4983230072969 + 3 ^ 40 * 2994798 * 2
def baseEnd_2994798 : Nat := 1537770837123679072752181

theorem tailTrace_2994798 : CollatzResearch.WordTrace tailWord_2994798 prefixEnd_2994798 1537770837123679072752181 := by
  unfold tailWord_2994798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653657075545723952905131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72819504402910527748827365 13653657075545723952905131)
  ·
    refine ⟨20480485613318585929357697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13653657075545723952905131 20480485613318585929357697)
    ·
      refine ⟨15360364209988939447018273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20480485613318585929357697 15360364209988939447018273)
      ·
        refine ⟨11520273157491704585263705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15360364209988939447018273 11520273157491704585263705)
        ·
          refine ⟨8640204868118778438947779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11520273157491704585263705 8640204868118778438947779)
          ·
            refine ⟨12960307302178167658421669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640204868118778438947779 12960307302178167658421669)
            ·
              refine ⟨2430057619158406435954063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12960307302178167658421669 2430057619158406435954063)
              ·
                refine ⟨3645086428737609653931095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430057619158406435954063 3645086428737609653931095)
                ·
                  refine ⟨5467629643106414480896643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645086428737609653931095 5467629643106414480896643)
                  ·
                    refine ⟨8201444464659621721344965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5467629643106414480896643 8201444464659621721344965)
                    ·
                      refine ⟨1537770837123679072752181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8201444464659621721344965 1537770837123679072752181)
                      ·
                        rfl

theorem cell23_2994798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2994798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994798 prefixEnd_2994798 := by exact prefixLift 2994798
  have htrace : WordTrace (prefixWord ++ tailWord_2994798) baseStart_2994798 baseEnd_2994798 := by
    simpa [prefixWord, tailWord_2994798, baseEnd_2994798] using wordTrace_append hprefix tailTrace_2994798
  have hstable : (prefixWord ++ tailWord_2994798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994798).length < 2 ^ (prefixWord ++ tailWord_2994798).sum := by decide
  have hdescent : baseEnd_2994798 < baseStart_2994798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994844 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2994844 : Nat := 118140960795 + 2994844 * 2 ^ 59
def prefixEnd_2994844 : Nat := 4983230072969 + 3 ^ 40 * 2994844 * 2
def baseEnd_2994844 : Nat := 1537794457233785892776969

theorem tailTrace_2994844 : CollatzResearch.WordTrace tailWord_2994844 prefixEnd_2994844 1537794457233785892776969 := by
  unfold tailWord_2994844
  simp only [CollatzResearch.WordTrace]
  refine ⟨54615467181099570739707793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72820622908132760986277057 54615467181099570739707793)
  ·
    refine ⟨40961600385824678054780845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54615467181099570739707793 40961600385824678054780845)
    ·
      refine ⟨15360600144684254270542817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40961600385824678054780845 15360600144684254270542817)
      ·
        refine ⟨11520450108513190702907113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15360600144684254270542817 11520450108513190702907113)
        ·
          refine ⟨8640337581384893027180335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11520450108513190702907113 8640337581384893027180335)
          ·
            refine ⟨12960506372077339540770503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640337581384893027180335 12960506372077339540770503)
            ·
              refine ⟨19440759558116009311155755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12960506372077339540770503 19440759558116009311155755)
              ·
                refine ⟨29161139337174013966733633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19440759558116009311155755 29161139337174013966733633)
                ·
                  refine ⟨21870854502880510475050225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29161139337174013966733633 21870854502880510475050225)
                  ·
                    refine ⟨16403140877160382856287669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21870854502880510475050225 16403140877160382856287669)
                    ·
                      refine ⟨1537794457233785892776969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16403140877160382856287669 1537794457233785892776969)
                      ·
                        rfl

theorem cell23_2994844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2994844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994844 prefixEnd_2994844 := by exact prefixLift 2994844
  have htrace : WordTrace (prefixWord ++ tailWord_2994844) baseStart_2994844 baseEnd_2994844 := by
    simpa [prefixWord, tailWord_2994844, baseEnd_2994844] using wordTrace_append hprefix tailTrace_2994844
  have hstable : (prefixWord ++ tailWord_2994844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994844).length < 2 ^ (prefixWord ++ tailWord_2994844).sum := by decide
  have hdescent : baseEnd_2994844 < baseStart_2994844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994849 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2994849 : Nat := 118140960795 + 2994849 * 2 ^ 59
def prefixEnd_2994849 : Nat := 4983230072969 + 3 ^ 40 * 2994849 * 2
def baseEnd_2994849 : Nat := 1537797024637058373214447

theorem tailTrace_2994849 : CollatzResearch.WordTrace tailWord_2994849 prefixEnd_2994849 1537797024637058373214447 := by
  unfold tailWord_2994849
  simp only [CollatzResearch.WordTrace]
  refine ⟨109231116727181027333347601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72820744484787351555565067 109231116727181027333347601)
  ·
    refine ⟨81923337545385770500010701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109231116727181027333347601 81923337545385770500010701)
    ·
      refine ⟨30721251579519663937504013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81923337545385770500010701 30721251579519663937504013)
      ·
        refine ⟨11520469342319873976564005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30721251579519663937504013 11520469342319873976564005)
        ·
          refine ⟨2160088001684976370605751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11520469342319873976564005 2160088001684976370605751)
          ·
            refine ⟨3240132002527464555908627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160088001684976370605751 3240132002527464555908627)
            ·
              refine ⟨4860198003791196833862941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240132002527464555908627 4860198003791196833862941)
              ·
                refine ⟨1822574251421698812698603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4860198003791196833862941 1822574251421698812698603)
                ·
                  refine ⟨2733861377132548219047905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822574251421698812698603 2733861377132548219047905)
                  ·
                    refine ⟨2050396032849411164285929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2733861377132548219047905 2050396032849411164285929)
                    ·
                      refine ⟨1537797024637058373214447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050396032849411164285929 1537797024637058373214447)
                      ·
                        rfl

theorem cell23_2994849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2994849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994849 prefixEnd_2994849 := by exact prefixLift 2994849
  have htrace : WordTrace (prefixWord ++ tailWord_2994849) baseStart_2994849 baseEnd_2994849 := by
    simpa [prefixWord, tailWord_2994849, baseEnd_2994849] using wordTrace_append hprefix tailTrace_2994849
  have hstable : (prefixWord ++ tailWord_2994849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994849).length < 2 ^ (prefixWord ++ tailWord_2994849).sum := by decide
  have hdescent : baseEnd_2994849 < baseStart_2994849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994857 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_2994857 : Nat := 118140960795 + 2994857 * 2 ^ 59
def prefixEnd_2994857 : Nat := 4983230072969 + 3 ^ 40 * 2994857 * 2
def baseEnd_2994857 : Nat := 1537801132482294341914409

theorem tailTrace_2994857 : CollatzResearch.WordTrace tailWord_2994857 prefixEnd_2994857 1537801132482294341914409 := by
  unfold tailWord_2994857
  simp only [CollatzResearch.WordTrace]
  refine ⟨109231408511152044699638825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72820939007434696466425883 109231408511152044699638825)
  ·
    refine ⟨81923556383364033524729119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109231408511152044699638825 81923556383364033524729119)
    ·
      refine ⟨122885334575046050287093679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81923556383364033524729119 122885334575046050287093679)
      ·
        refine ⟨184328001862569075430640519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122885334575046050287093679 184328001862569075430640519)
        ·
          refine ⟨276492002793853613145960779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184328001862569075430640519 276492002793853613145960779)
          ·
            refine ⟨414738004190780419718941169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276492002793853613145960779 414738004190780419718941169)
            ·
              refine ⟨311053503143085314789205877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414738004190780419718941169 311053503143085314789205877)
              ·
                refine ⟨29161265919664248261488051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311053503143085314789205877 29161265919664248261488051)
                ·
                  refine ⟨43741898879496372392232077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29161265919664248261488051 43741898879496372392232077)
                  ·
                    refine ⟨16403212079811139647087029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43741898879496372392232077 16403212079811139647087029)
                    ·
                      refine ⟨1537801132482294341914409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16403212079811139647087029 1537801132482294341914409)
                      ·
                        rfl

theorem cell23_2994857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_2994857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994857 prefixEnd_2994857 := by exact prefixLift 2994857
  have htrace : WordTrace (prefixWord ++ tailWord_2994857) baseStart_2994857 baseEnd_2994857 := by
    simpa [prefixWord, tailWord_2994857, baseEnd_2994857] using wordTrace_append hprefix tailTrace_2994857
  have hstable : (prefixWord ++ tailWord_2994857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994857).length < 2 ^ (prefixWord ++ tailWord_2994857).sum := by decide
  have hdescent : baseEnd_2994857 < baseStart_2994857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994874 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_2994874 : Nat := 118140960795 + 2994874 * 2 ^ 59
def prefixEnd_2994874 : Nat := 4983230072969 + 3 ^ 40 * 2994874 * 2
def baseEnd_2994874 : Nat := 1537809861653420775401831

theorem tailTrace_2994874 : CollatzResearch.WordTrace tailWord_2994874 prefixEnd_2994874 1537809861653420775401831 := by
  unfold tailWord_2994874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27308007138022614150751919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72821352368060304402005117 27308007138022614150751919)
  ·
    refine ⟨40962010707033921226127879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27308007138022614150751919 40962010707033921226127879)
    ·
      refine ⟨61443016060550881839191819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40962010707033921226127879 61443016060550881839191819)
      ·
        refine ⟨92164524090826322758787729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61443016060550881839191819 92164524090826322758787729)
        ·
          refine ⟨69123393068119742069090797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92164524090826322758787729 69123393068119742069090797)
          ·
            refine ⟨25921272400544903275909049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69123393068119742069090797 25921272400544903275909049)
            ·
              refine ⟨19440954300408677456931787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25921272400544903275909049 19440954300408677456931787)
              ·
                refine ⟨29161431450613016185397681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19440954300408677456931787 29161431450613016185397681)
                ·
                  refine ⟨21871073587959762139048261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29161431450613016185397681 21871073587959762139048261)
                  ·
                    refine ⟨4100826297742455401071549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21871073587959762139048261 4100826297742455401071549)
                    ·
                      refine ⟨1537809861653420775401831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100826297742455401071549 1537809861653420775401831)
                      ·
                        rfl

theorem cell23_2994874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_2994874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994874 prefixEnd_2994874 := by exact prefixLift 2994874
  have htrace : WordTrace (prefixWord ++ tailWord_2994874) baseStart_2994874 baseEnd_2994874 := by
    simpa [prefixWord, tailWord_2994874, baseEnd_2994874] using wordTrace_append hprefix tailTrace_2994874
  have hstable : (prefixWord ++ tailWord_2994874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994874).length < 2 ^ (prefixWord ++ tailWord_2994874).sum := by decide
  have hdescent : baseEnd_2994874 < baseStart_2994874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994961 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_2994961 : Nat := 118140960795 + 2994961 * 2 ^ 59
def prefixEnd_2994961 : Nat := 4983230072969 + 3 ^ 40 * 2994961 * 2
def baseEnd_2994961 : Nat := 1537854534470361935013931

theorem tailTrace_2994961 : CollatzResearch.WordTrace tailWord_2994961 prefixEnd_2994961 1537854534470361935013931 := by
  unfold tailWord_2994961
  simp only [CollatzResearch.WordTrace]
  refine ⟨109235201702775270461424737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72823467801850180307616491 109235201702775270461424737)
  ·
    refine ⟨81926401277081452846068553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109235201702775270461424737 81926401277081452846068553)
    ·
      refine ⟨61444800957811089634551415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81926401277081452846068553 61444800957811089634551415)
      ·
        refine ⟨92167201436716634451827123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61444800957811089634551415 92167201436716634451827123)
        ·
          refine ⟨138250802155074951677740685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92167201436716634451827123 138250802155074951677740685)
          ·
            refine ⟨51844050808153106879152757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138250802155074951677740685 51844050808153106879152757)
            ·
              refine ⟨4860379763264353769920571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51844050808153106879152757 4860379763264353769920571)
              ·
                refine ⟨7290569644896530654880857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860379763264353769920571 7290569644896530654880857)
                ·
                  refine ⟨5467927233672397991160643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7290569644896530654880857 5467927233672397991160643)
                  ·
                    refine ⟨8201890850508596986740965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5467927233672397991160643 8201890850508596986740965)
                    ·
                      refine ⟨1537854534470361935013931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8201890850508596986740965 1537854534470361935013931)
                      ·
                        rfl

theorem cell23_2994961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_2994961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994961 prefixEnd_2994961 := by exact prefixLift 2994961
  have htrace : WordTrace (prefixWord ++ tailWord_2994961) baseStart_2994961 baseEnd_2994961 := by
    simpa [prefixWord, tailWord_2994961, baseEnd_2994961] using wordTrace_append hprefix tailTrace_2994961
  have hstable : (prefixWord ++ tailWord_2994961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994961).length < 2 ^ (prefixWord ++ tailWord_2994961).sum := by decide
  have hdescent : baseEnd_2994961 < baseStart_2994961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994978 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_2994978 : Nat := 118140960795 + 2994978 * 2 ^ 59
def prefixEnd_2994978 : Nat := 4983230072969 + 3 ^ 40 * 2994978 * 2
def baseEnd_2994978 : Nat := 1537863263641488368501353

theorem tailTrace_2994978 : CollatzResearch.WordTrace tailWord_2994978 prefixEnd_2994978 1537863263641488368501353 := by
  unfold tailWord_2994978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27308955435928420591198397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72823881162475788243195725 27308955435928420591198397)
  ·
    refine ⟨10240858288473157721699399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27308955435928420591198397 10240858288473157721699399)
    ·
      refine ⟨15361287432709736582549099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10240858288473157721699399 15361287432709736582549099)
      ·
        refine ⟨23041931149064604873823649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15361287432709736582549099 23041931149064604873823649)
        ·
          refine ⟨17281448361798453655367737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23041931149064604873823649 17281448361798453655367737)
          ·
            refine ⟨12961086271348840241525803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17281448361798453655367737 12961086271348840241525803)
            ·
              refine ⟨19441629407023260362288705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12961086271348840241525803 19441629407023260362288705)
              ·
                refine ⟨14581222055267445271716529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19441629407023260362288705 14581222055267445271716529)
                ·
                  refine ⟨10935916541450583953787397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14581222055267445271716529 10935916541450583953787397)
                  ·
                    refine ⟨2050484351521984491335137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10935916541450583953787397 2050484351521984491335137)
                    ·
                      refine ⟨1537863263641488368501353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050484351521984491335137 1537863263641488368501353)
                      ·
                        rfl

theorem cell23_2994978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_2994978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994978 prefixEnd_2994978 := by exact prefixLift 2994978
  have htrace : WordTrace (prefixWord ++ tailWord_2994978) baseStart_2994978 baseEnd_2994978 := by
    simpa [prefixWord, tailWord_2994978, baseEnd_2994978] using wordTrace_append hprefix tailTrace_2994978
  have hstable : (prefixWord ++ tailWord_2994978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994978).length < 2 ^ (prefixWord ++ tailWord_2994978).sum := by decide
  have hdescent : baseEnd_2994978 < baseStart_2994978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994981 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_2994981 : Nat := 118140960795 + 2994981 * 2 ^ 59
def prefixEnd_2994981 : Nat := 4983230072969 + 3 ^ 40 * 2994981 * 2
def baseEnd_2994981 : Nat := 1537864804083451856763839

theorem tailTrace_2994981 : CollatzResearch.WordTrace tailWord_2994981 prefixEnd_2994981 1537864804083451856763839 := by
  unfold tailWord_2994981
  simp only [CollatzResearch.WordTrace]
  refine ⟨109235931162702813877152797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72823954108468542584768531 109235931162702813877152797)
  ·
    refine ⟨40963474186013555203932299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109235931162702813877152797 40963474186013555203932299)
    ·
      refine ⟨61445211279020332805898449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40963474186013555203932299 61445211279020332805898449)
      ·
        refine ⟨46083908459265249604423837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61445211279020332805898449 46083908459265249604423837)
        ·
          refine ⟨17281465672224468601658939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46083908459265249604423837 17281465672224468601658939)
          ·
            refine ⟨25922198508336702902488409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17281465672224468601658939 25922198508336702902488409)
            ·
              refine ⟨19441648881252527176866307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25922198508336702902488409 19441648881252527176866307)
              ·
                refine ⟨29162473321878790765299461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19441648881252527176866307 29162473321878790765299461)
                ·
                  refine ⟨5467963747852273268493649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29162473321878790765299461 5467963747852273268493649)
                  ·
                    refine ⟨4100972810889204951370237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467963747852273268493649 4100972810889204951370237)
                    ·
                      refine ⟨1537864804083451856763839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4100972810889204951370237 1537864804083451856763839)
                      ·
                        rfl

theorem cell23_2994981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_2994981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994981 prefixEnd_2994981 := by exact prefixLift 2994981
  have htrace : WordTrace (prefixWord ++ tailWord_2994981) baseStart_2994981 baseEnd_2994981 := by
    simpa [prefixWord, tailWord_2994981, baseEnd_2994981] using wordTrace_append hprefix tailTrace_2994981
  have hstable : (prefixWord ++ tailWord_2994981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994981).length < 2 ^ (prefixWord ++ tailWord_2994981).sum := by decide
  have hdescent : baseEnd_2994981 < baseStart_2994981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994988 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_2994988 : Nat := 118140960795 + 2994988 * 2 ^ 59
def prefixEnd_2994988 : Nat := 4983230072969 + 3 ^ 40 * 2994988 * 2
def baseEnd_2994988 : Nat := 512622799482677776458769

theorem tailTrace_2994988 : CollatzResearch.WordTrace tailWord_2994988 prefixEnd_2994988 512622799482677776458769 := by
  unfold tailWord_2994988
  simp only [CollatzResearch.WordTrace]
  refine ⟨54618093236838727036328809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72824124315784969381771745 54618093236838727036328809)
  ·
    refine ⟨40963569927629045277246607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54618093236838727036328809 40963569927629045277246607)
    ·
      refine ⟨61445354891443567915869911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40963569927629045277246607 61445354891443567915869911)
      ·
        refine ⟨92168032337165351873804867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61445354891443567915869911 92168032337165351873804867)
        ·
          refine ⟨138252048505748027810707301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92168032337165351873804867 138252048505748027810707301)
          ·
            refine ⟨25922259094827755214507619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138252048505748027810707301 25922259094827755214507619)
            ·
              refine ⟨38883388642241632821761429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25922259094827755214507619 38883388642241632821761429)
              ·
                refine ⟨1822658842605076538520067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38883388642241632821761429 1822658842605076538520067)
                ·
                  refine ⟨2733988263907614807780101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822658842605076538520067 2733988263907614807780101)
                  ·
                    refine ⟨512622799482677776458769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2733988263907614807780101 512622799482677776458769)
                    ·
                      rfl

theorem cell23_2994988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_2994988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2994988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2994988 prefixEnd_2994988 := by exact prefixLift 2994988
  have htrace : WordTrace (prefixWord ++ tailWord_2994988) baseStart_2994988 baseEnd_2994988 := by
    simpa [prefixWord, tailWord_2994988, baseEnd_2994988] using wordTrace_append hprefix tailTrace_2994988
  have hstable : (prefixWord ++ tailWord_2994988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994988).length < 2 ^ (prefixWord ++ tailWord_2994988).sum := by decide
  have hdescent : baseEnd_2994988 < baseStart_2994988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995004 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2995004 : Nat := 118140960795 + 2995004 * 2 ^ 59
def prefixEnd_2995004 : Nat := 4983230072969 + 3 ^ 40 * 2995004 * 2
def baseEnd_2995004 : Nat := 1537876614138505266776233

theorem tailTrace_2995004 : CollatzResearch.WordTrace tailWord_2995004 prefixEnd_2995004 1537876614138505266776233 := by
  unfold tailWord_2995004
  simp only [CollatzResearch.WordTrace]
  refine ⟨54618385020809744402620033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72824513361079659203493377 54618385020809744402620033)
  ·
    refine ⟨40963788765607308301965025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54618385020809744402620033 40963788765607308301965025)
    ·
      refine ⟨30722841574205481226473769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40963788765607308301965025 30722841574205481226473769)
      ·
        refine ⟨23042131180654110919855327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30722841574205481226473769 23042131180654110919855327)
        ·
          refine ⟨34563196770981166379782991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23042131180654110919855327 34563196770981166379782991)
          ·
            refine ⟨51844795156471749569674487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34563196770981166379782991 51844795156471749569674487)
            ·
              refine ⟨77767192734707624354511731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51844795156471749569674487 77767192734707624354511731)
              ·
                refine ⟨116650789102061436531767597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77767192734707624354511731 116650789102061436531767597)
                ·
                  refine ⟨43744045913273038699412849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116650789102061436531767597 43744045913273038699412849)
                  ·
                    refine ⟨32808034434954779024559637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43744045913273038699412849 32808034434954779024559637)
                    ·
                      refine ⟨1537876614138505266776233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32808034434954779024559637 1537876614138505266776233)
                      ·
                        rfl

theorem cell23_2995004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2995004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995004 prefixEnd_2995004 := by exact prefixLift 2995004
  have htrace : WordTrace (prefixWord ++ tailWord_2995004) baseStart_2995004 baseEnd_2995004 := by
    simpa [prefixWord, tailWord_2995004, baseEnd_2995004] using wordTrace_append hprefix tailTrace_2995004
  have hstable : (prefixWord ++ tailWord_2995004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995004).length < 2 ^ (prefixWord ++ tailWord_2995004).sum := by decide
  have hdescent : baseEnd_2995004 < baseStart_2995004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995045 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 1, 1, 3]
def baseStart_2995045 : Nat := 118140960795 + 2995045 * 2 ^ 59
def prefixEnd_2995045 : Nat := 4983230072969 + 3 ^ 40 * 2995045 * 2
def baseEnd_2995045 : Nat := 1537897666845339606363545

theorem tailTrace_2995045 : CollatzResearch.WordTrace tailWord_2995045 prefixEnd_2995045 1537897666845339606363545 := by
  unfold tailWord_2995045
  simp only [CollatzResearch.WordTrace]
  refine ⟨109238265434470952807482589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72825510289647301871655059 109238265434470952807482589)
  ·
    refine ⟨40964349537926607302805971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109238265434470952807482589 40964349537926607302805971)
    ·
      refine ⟨61446524306889910954208957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40964349537926607302805971 61446524306889910954208957)
      ·
        refine ⟨23042446615083716607828359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61446524306889910954208957 23042446615083716607828359)
        ·
          refine ⟨34563669922625574911742539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23042446615083716607828359 34563669922625574911742539)
          ·
            refine ⟨51845504883938362367613809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34563669922625574911742539 51845504883938362367613809)
            ·
              refine ⟨38884128662953771775710357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51845504883938362367613809 38884128662953771775710357)
              ·
                refine ⟨1822693531075958051986423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38884128662953771775710357 1822693531075958051986423)
                ·
                  refine ⟨2734040296613937077979635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822693531075958051986423 2734040296613937077979635)
                  ·
                    refine ⟨4101060444920905616969453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2734040296613937077979635 4101060444920905616969453)
                    ·
                      refine ⟨1537897666845339606363545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4101060444920905616969453 1537897666845339606363545)
                      ·
                        rfl

theorem cell23_2995045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_2995045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995045 prefixEnd_2995045 := by exact prefixLift 2995045
  have htrace : WordTrace (prefixWord ++ tailWord_2995045) baseStart_2995045 baseEnd_2995045 := by
    simpa [prefixWord, tailWord_2995045, baseEnd_2995045] using wordTrace_append hprefix tailTrace_2995045
  have hstable : (prefixWord ++ tailWord_2995045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995045).length < 2 ^ (prefixWord ++ tailWord_2995045).sum := by decide
  have hdescent : baseEnd_2995045 < baseStart_2995045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995081 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_2995081 : Nat := 118140960795 + 2995081 * 2 ^ 59
def prefixEnd_2995081 : Nat := 4983230072969 + 3 ^ 40 * 2995081 * 2
def baseEnd_2995081 : Nat := 1537916152148901465513379

theorem tailTrace_2995081 : CollatzResearch.WordTrace tailWord_2995081 prefixEnd_2995081 1537916152148901465513379 := by
  unfold tailWord_2995081
  simp only [CollatzResearch.WordTrace]
  refine ⟨109239578462340530955793097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72826385641560353970528731 109239578462340530955793097)
  ·
    refine ⟨81929683846755398216844823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109239578462340530955793097 81929683846755398216844823)
    ·
      refine ⟨122894525770133097325267235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81929683846755398216844823 122894525770133097325267235)
      ·
        refine ⟨184341788655199645987900853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122894525770133097325267235 184341788655199645987900853)
        ·
          refine ⟨17282042686424966811365705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184341788655199645987900853 17282042686424966811365705)
          ·
            refine ⟨12961532014818725108524279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17282042686424966811365705 12961532014818725108524279)
            ·
              refine ⟨19442298022228087662786419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12961532014818725108524279 19442298022228087662786419)
              ·
                refine ⟨29163447033342131494179629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19442298022228087662786419 29163447033342131494179629)
                ·
                  refine ⟨10936292637503299310317361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29163447033342131494179629 10936292637503299310317361)
                  ·
                    refine ⟨8202219478127474482738021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10936292637503299310317361 8202219478127474482738021)
                    ·
                      refine ⟨1537916152148901465513379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8202219478127474482738021 1537916152148901465513379)
                      ·
                        rfl

theorem cell23_2995081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_2995081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995081 prefixEnd_2995081 := by exact prefixLift 2995081
  have htrace : WordTrace (prefixWord ++ tailWord_2995081) baseStart_2995081 baseEnd_2995081 := by
    simpa [prefixWord, tailWord_2995081, baseEnd_2995081] using wordTrace_append hprefix tailTrace_2995081
  have hstable : (prefixWord ++ tailWord_2995081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995081).length < 2 ^ (prefixWord ++ tailWord_2995081).sum := by decide
  have hdescent : baseEnd_2995081 < baseStart_2995081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995151 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 2, 6]
def baseStart_2995151 : Nat := 118140960795 + 2995151 * 2 ^ 59
def prefixEnd_2995151 : Nat := 4983230072969 + 3 ^ 40 * 2995151 * 2
def baseEnd_2995151 : Nat := 512650698598238730546019

theorem tailTrace_2995151 : CollatzResearch.WordTrace tailWord_2995151 prefixEnd_2995151 512650698598238730546019 := by
  unfold tailWord_2995151
  simp only [CollatzResearch.WordTrace]
  refine ⟨109242131572086932910841307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72828087714724621940560871 109242131572086932910841307)
  ·
    refine ⟨163863197358130399366261961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109242131572086932910841307 163863197358130399366261961)
    ·
      refine ⟨122897398018597799524696471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163863197358130399366261961 122897398018597799524696471)
      ·
        refine ⟨184346097027896699287044707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122897398018597799524696471 184346097027896699287044707)
        ·
          refine ⟨276519145541845048930567061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184346097027896699287044707 276519145541845048930567061)
          ·
            refine ⟨12961834947273986668620331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 276519145541845048930567061 12961834947273986668620331)
            ·
              refine ⟨19442752420910980002930497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12961834947273986668620331 19442752420910980002930497)
              ·
                refine ⟨14582064315683235002197873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19442752420910980002930497 14582064315683235002197873)
                ·
                  refine ⟨10936548236762426251648405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14582064315683235002197873 10936548236762426251648405)
                  ·
                    refine ⟨512650698598238730546019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10936548236762426251648405 512650698598238730546019)
                    ·
                      rfl

theorem cell23_2995151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_2995151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995151 prefixEnd_2995151 := by exact prefixLift 2995151
  have htrace : WordTrace (prefixWord ++ tailWord_2995151) baseStart_2995151 baseEnd_2995151 := by
    simpa [prefixWord, tailWord_2995151, baseEnd_2995151] using wordTrace_append hprefix tailTrace_2995151
  have hstable : (prefixWord ++ tailWord_2995151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995151).length < 2 ^ (prefixWord ++ tailWord_2995151).sum := by decide
  have hdescent : baseEnd_2995151 < baseStart_2995151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995282 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_2995282 : Nat := 118140960795 + 2995282 * 2 ^ 59
def prefixEnd_2995282 : Nat := 4983230072969 + 3 ^ 40 * 2995282 * 2
def baseEnd_2995282 : Nat := 1538019361760455179099955

theorem tailTrace_2995282 : CollatzResearch.WordTrace tailWord_2995282 prefixEnd_2995282 1538019361760455179099955 := by
  unfold tailWord_2995282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27311727383653085570965025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72831273023074894855906733 27311727383653085570965025)
  ·
    refine ⟨20483795537739814178223769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27311727383653085570965025 20483795537739814178223769)
    ·
      refine ⟨15362846653304860633667827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20483795537739814178223769 15362846653304860633667827)
      ·
        refine ⟨23044269979957290950501741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362846653304860633667827 23044269979957290950501741)
        ·
          refine ⟨8641601242483984106438153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23044269979957290950501741 8641601242483984106438153)
          ·
            refine ⟨6481200931862988079828615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8641601242483984106438153 6481200931862988079828615)
            ·
              refine ⟨9721801397794482119742923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481200931862988079828615 9721801397794482119742923)
              ·
                refine ⟨14582702096691723179614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9721801397794482119742923 14582702096691723179614385)
                ·
                  refine ⟨10937026572518792384710789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14582702096691723179614385 10937026572518792384710789)
                  ·
                    refine ⟨2050692482347273572133273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10937026572518792384710789 2050692482347273572133273)
                    ·
                      refine ⟨1538019361760455179099955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050692482347273572133273 1538019361760455179099955)
                      ·
                        rfl

theorem cell23_2995282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_2995282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995282 prefixEnd_2995282 := by exact prefixLift 2995282
  have htrace : WordTrace (prefixWord ++ tailWord_2995282) baseStart_2995282 baseEnd_2995282 := by
    simpa [prefixWord, tailWord_2995282, baseEnd_2995282] using wordTrace_append hprefix tailTrace_2995282
  have hstable : (prefixWord ++ tailWord_2995282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995282).length < 2 ^ (prefixWord ++ tailWord_2995282).sum := by decide
  have hdescent : baseEnd_2995282 < baseStart_2995282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995288 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 6]
def baseStart_2995288 : Nat := 118140960795 + 2995288 * 2 ^ 59
def prefixEnd_2995288 : Nat := 4983230072969 + 3 ^ 40 * 2995288 * 2
def baseEnd_2995288 : Nat := 170891382516042461736103

theorem tailTrace_2995288 : CollatzResearch.WordTrace tailWord_2995288 prefixEnd_2995288 170891382516042461736103 := by
  unfold tailWord_2995288
  simp only [CollatzResearch.WordTrace]
  refine ⟨54623564186295302654289259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72831418915060403539052345 54623564186295302654289259)
  ·
    refine ⟨81935346279442953981433889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54623564186295302654289259 81935346279442953981433889)
    ·
      refine ⟨61451509709582215486075417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81935346279442953981433889 61451509709582215486075417)
      ·
        refine ⟨46088632282186661614556563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61451509709582215486075417 46088632282186661614556563)
        ·
          refine ⟨69132948423279992421834845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46088632282186661614556563 69132948423279992421834845)
          ·
            refine ⟨25924855658729997158188067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69132948423279992421834845 25924855658729997158188067)
            ·
              refine ⟨38887283488094995737282101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25924855658729997158188067 38887283488094995737282101)
              ·
                refine ⟨3645682827008905850370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38887283488094995737282101 3645682827008905850370197)
                ·
                  refine ⟨170891382516042461736103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3645682827008905850370197 170891382516042461736103)
                  ·
                    rfl

theorem cell23_2995288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 6].length) (baseStart_2995288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995288 prefixEnd_2995288 := by exact prefixLift 2995288
  have htrace : WordTrace (prefixWord ++ tailWord_2995288) baseStart_2995288 baseEnd_2995288 := by
    simpa [prefixWord, tailWord_2995288, baseEnd_2995288] using wordTrace_append hprefix tailTrace_2995288
  have hstable : (prefixWord ++ tailWord_2995288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995288).length < 2 ^ (prefixWord ++ tailWord_2995288).sum := by decide
  have hdescent : baseEnd_2995288 < baseStart_2995288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995309 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2995309 : Nat := 118140960795 + 2995309 * 2 ^ 59
def prefixEnd_2995309 : Nat := 4983230072969 + 3 ^ 40 * 2995309 * 2
def baseEnd_2995309 : Nat := 512677741912708857820777

theorem tailTrace_2995309 : CollatzResearch.WordTrace tailWord_2995309 prefixEnd_2995309 512677741912708857820777 := by
  unfold tailWord_2995309
  simp only [CollatzResearch.WordTrace]
  refine ⟨109247894305514525895092981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72831929537009683930061987 109247894305514525895092981)
  ·
    refine ⟨10241990091141986802664967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109247894305514525895092981 10241990091141986802664967)
    ·
      refine ⟨15362985136712980203997451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10241990091141986802664967 15362985136712980203997451)
      ·
        refine ⟨23044477705069470305996177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362985136712980203997451 23044477705069470305996177)
        ·
          refine ⟨17283358278802102729497133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23044477705069470305996177 17283358278802102729497133)
          ·
            refine ⟨6481259354550788523561425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17283358278802102729497133 6481259354550788523561425)
            ·
              refine ⟨4860944515913091392671069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6481259354550788523561425 4860944515913091392671069)
              ·
                refine ⟨1822854193467409272251651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4860944515913091392671069 1822854193467409272251651)
                ·
                  refine ⟨2734281290201113908377477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822854193467409272251651 2734281290201113908377477)
                  ·
                    refine ⟨512677741912708857820777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734281290201113908377477 512677741912708857820777)
                    ·
                      rfl

theorem cell23_2995309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2995309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995309 prefixEnd_2995309 := by exact prefixLift 2995309
  have htrace : WordTrace (prefixWord ++ tailWord_2995309) baseStart_2995309 baseEnd_2995309 := by
    simpa [prefixWord, tailWord_2995309, baseEnd_2995309] using wordTrace_append hprefix tailTrace_2995309
  have hstable : (prefixWord ++ tailWord_2995309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995309).length < 2 ^ (prefixWord ++ tailWord_2995309).sum := by decide
  have hdescent : baseEnd_2995309 < baseStart_2995309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995332 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_2995332 : Nat := 118140960795 + 2995332 * 2 ^ 59
def prefixEnd_2995332 : Nat := 4983230072969 + 3 ^ 40 * 2995332 * 2
def baseEnd_2995332 : Nat := 1538045035793179983474725

theorem tailTrace_2995332 : CollatzResearch.WordTrace tailWord_2995332 prefixEnd_2995332 1538045035793179983474725 := by
  unfold tailWord_2995332
  simp only [CollatzResearch.WordTrace]
  refine ⟨54624366592215600411590125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72832488789620800548786833 54624366592215600411590125)
  ·
    refine ⟨20484137472080850154346297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54624366592215600411590125 20484137472080850154346297)
    ·
      refine ⟨15363103104060637615759723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20484137472080850154346297 15363103104060637615759723)
      ·
        refine ⟨23044654656090956423639585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15363103104060637615759723 23044654656090956423639585)
        ·
          refine ⟨17283490992068217317729689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23044654656090956423639585 17283490992068217317729689)
          ·
            refine ⟨12962618244051162988297267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17283490992068217317729689 12962618244051162988297267)
            ·
              refine ⟨19443927366076744482445901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962618244051162988297267 19443927366076744482445901)
              ·
                refine ⟨7291472762278779180917213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19443927366076744482445901 7291472762278779180917213)
                ·
                  refine ⟨2734302285854542192843955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7291472762278779180917213 2734302285854542192843955)
                  ·
                    refine ⟨4101453428781813289265933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2734302285854542192843955 4101453428781813289265933)
                    ·
                      refine ⟨1538045035793179983474725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4101453428781813289265933 1538045035793179983474725)
                      ·
                        rfl

theorem cell23_2995332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_2995332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995332 prefixEnd_2995332 := by exact prefixLift 2995332
  have htrace : WordTrace (prefixWord ++ tailWord_2995332) baseStart_2995332 baseEnd_2995332 := by
    simpa [prefixWord, tailWord_2995332, baseEnd_2995332] using wordTrace_append hprefix tailTrace_2995332
  have hstable : (prefixWord ++ tailWord_2995332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995332).length < 2 ^ (prefixWord ++ tailWord_2995332).sum := by decide
  have hdescent : baseEnd_2995332 < baseStart_2995332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995342 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2995342 : Nat := 118140960795 + 2995342 * 2 ^ 59
def prefixEnd_2995342 : Nat := 4983230072969 + 3 ^ 40 * 2995342 * 2
def baseEnd_2995342 : Nat := 1538050170599724944349679

theorem tailTrace_2995342 : CollatzResearch.WordTrace tailWord_2995342 prefixEnd_2995342 1538050170599724944349679 := by
  unfold tailWord_2995342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13656137239299371566380535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72832731942929981687362853 13656137239299371566380535)
  ·
    refine ⟨20484205858949057349570803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13656137239299371566380535 20484205858949057349570803)
    ·
      refine ⟨30726308788423586024356205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484205858949057349570803 30726308788423586024356205)
      ·
        refine ⟨11522365795658844759133577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30726308788423586024356205 11522365795658844759133577)
        ·
          refine ⟨8641774346744133569350183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11522365795658844759133577 8641774346744133569350183)
          ·
            refine ⟨12962661520116200354025275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641774346744133569350183 12962661520116200354025275)
            ·
              refine ⟨19443992280174300531037913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962661520116200354025275 19443992280174300531037913)
              ·
                refine ⟨14582994210130725398278435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19443992280174300531037913 14582994210130725398278435)
                ·
                  refine ⟨21874491315196088097417653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14582994210130725398278435 21874491315196088097417653)
                  ·
                    refine ⟨2050733560799633259132905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21874491315196088097417653 2050733560799633259132905)
                    ·
                      refine ⟨1538050170599724944349679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050733560799633259132905 1538050170599724944349679)
                      ·
                        rfl

theorem cell23_2995342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2995342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995342 prefixEnd_2995342 := by exact prefixLift 2995342
  have htrace : WordTrace (prefixWord ++ tailWord_2995342) baseStart_2995342 baseEnd_2995342 := by
    simpa [prefixWord, tailWord_2995342, baseEnd_2995342] using wordTrace_append hprefix tailTrace_2995342
  have hstable : (prefixWord ++ tailWord_2995342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995342).length < 2 ^ (prefixWord ++ tailWord_2995342).sum := by decide
  have hdescent : baseEnd_2995342 < baseStart_2995342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995352 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 1, 5]
def baseStart_2995352 : Nat := 118140960795 + 2995352 * 2 ^ 59
def prefixEnd_2995352 : Nat := 4983230072969 + 3 ^ 40 * 2995352 * 2
def baseEnd_2995352 : Nat := 512685101802089968408211

theorem tailTrace_2995352 : CollatzResearch.WordTrace tailWord_2995352 prefixEnd_2995352 512685101802089968408211 := by
  unfold tailWord_2995352
  simp only [CollatzResearch.WordTrace]
  refine ⟨54624731322179372119454155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72832975096239162825938873 54624731322179372119454155)
  ·
    refine ⟨81937096983269058179181233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54624731322179372119454155 81937096983269058179181233)
    ·
      refine ⟨61452822737451793634385925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81937096983269058179181233 61452822737451793634385925)
      ·
        refine ⟨11522404263272211306447361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61452822737451793634385925 11522404263272211306447361)
        ·
          refine ⟨8641803197454158479835521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11522404263272211306447361 8641803197454158479835521)
          ·
            refine ⟨6481352398090618859876641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8641803197454158479835521 6481352398090618859876641)
            ·
              refine ⟨4861014298567964144907481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6481352398090618859876641 4861014298567964144907481)
              ·
                refine ⟨3645760723925973108680611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861014298567964144907481 3645760723925973108680611)
                ·
                  refine ⟨5468641085888959663020917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645760723925973108680611 5468641085888959663020917)
                  ·
                    refine ⟨512685101802089968408211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5468641085888959663020917 512685101802089968408211)
                    ·
                      rfl

theorem cell23_2995352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_2995352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995352 prefixEnd_2995352 := by exact prefixLift 2995352
  have htrace : WordTrace (prefixWord ++ tailWord_2995352) baseStart_2995352 baseEnd_2995352 := by
    simpa [prefixWord, tailWord_2995352, baseEnd_2995352] using wordTrace_append hprefix tailTrace_2995352
  have hstable : (prefixWord ++ tailWord_2995352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995352).length < 2 ^ (prefixWord ++ tailWord_2995352).sum := by decide
  have hdescent : baseEnd_2995352 < baseStart_2995352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995365 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_2995365 : Nat := 118140960795 + 2995365 * 2 ^ 59
def prefixEnd_2995365 : Nat := 4983230072969 + 3 ^ 40 * 2995365 * 2
def baseEnd_2995365 : Nat := 512687326884926118120691

theorem tailTrace_2995365 : CollatzResearch.WordTrace tailWord_2995365 prefixEnd_2995365 512687326884926118120691 := by
  unfold tailWord_2995365
  simp only [CollatzResearch.WordTrace]
  refine ⟨109249936793311647459131549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72833291195541098306087699 109249936793311647459131549)
  ·
    refine ⟨40968726297491867797174331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109249936793311647459131549 40968726297491867797174331)
    ·
      refine ⟨61453089446237801695761497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40968726297491867797174331 61453089446237801695761497)
      ·
        refine ⟨46089817084678351271821123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61453089446237801695761497 46089817084678351271821123)
        ·
          refine ⟨69134725627017526907731685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46089817084678351271821123 69134725627017526907731685)
          ·
            refine ⟨12962761055065786295199691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69134725627017526907731685 12962761055065786295199691)
            ·
              refine ⟨19444141582598679442799537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962761055065786295199691 19444141582598679442799537)
              ·
                refine ⟨14583106186949009582099653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19444141582598679442799537 14583106186949009582099653)
                ·
                  refine ⟨2734332410052939296643685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14583106186949009582099653 2734332410052939296643685)
                  ·
                    refine ⟨512687326884926118120691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734332410052939296643685 512687326884926118120691)
                    ·
                      rfl

theorem cell23_2995365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_2995365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995365 prefixEnd_2995365 := by exact prefixLift 2995365
  have htrace : WordTrace (prefixWord ++ tailWord_2995365) baseStart_2995365 baseEnd_2995365 := by
    simpa [prefixWord, tailWord_2995365, baseEnd_2995365] using wordTrace_append hprefix tailTrace_2995365
  have hstable : (prefixWord ++ tailWord_2995365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995365).length < 2 ^ (prefixWord ++ tailWord_2995365).sum := by decide
  have hdescent : baseEnd_2995365 < baseStart_2995365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995378 : List Nat := [3, 2, 1, 1, 1, 4, 11]
def baseStart_2995378 : Nat := 118140960795 + 2995378 * 2 ^ 59
def prefixEnd_2995378 : Nat := 4983230072969 + 3 ^ 40 * 2995378 * 2
def baseEnd_2995378 : Nat := 18988501924731935845673

theorem tailTrace_2995378 : CollatzResearch.WordTrace tailWord_2995378 prefixEnd_2995378 18988501924731935845673 := by
  unfold tailWord_2995378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27312602735566137669838697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72833607294843033786236525 27312602735566137669838697)
  ·
    refine ⟨20484452051674603252379023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27312602735566137669838697 20484452051674603252379023)
    ·
      refine ⟨30726678077511904878568535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484452051674603252379023 30726678077511904878568535)
      ·
        refine ⟨46090017116267857317852803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30726678077511904878568535 46090017116267857317852803)
        ·
          refine ⟨69135025674401785976779205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46090017116267857317852803 69135025674401785976779205)
          ·
            refine ⟨12962817313950334870646101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69135025674401785976779205 12962817313950334870646101)
            ·
              refine ⟨18988501924731935845673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12962817313950334870646101 18988501924731935845673)
              ·
                rfl

theorem cell23_2995378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 11].length) (baseStart_2995378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995378 prefixEnd_2995378 := by exact prefixLift 2995378
  have htrace : WordTrace (prefixWord ++ tailWord_2995378) baseStart_2995378 baseEnd_2995378 := by
    simpa [prefixWord, tailWord_2995378, baseEnd_2995378] using wordTrace_append hprefix tailTrace_2995378
  have hstable : (prefixWord ++ tailWord_2995378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995378).length < 2 ^ (prefixWord ++ tailWord_2995378).sum := by decide
  have hdescent : baseEnd_2995378 < baseStart_2995378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995389 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_2995389 : Nat := 118140960795 + 2995389 * 2 ^ 59
def prefixEnd_2995389 : Nat := 4983230072969 + 3 ^ 40 * 2995389 * 2
def baseEnd_2995389 : Nat := 1538074304190486260461963

theorem tailTrace_2995389 : CollatzResearch.WordTrace tailWord_2995389 prefixEnd_2995389 1538074304190486260461963 := by
  unfold tailWord_2995389
  simp only [CollatzResearch.WordTrace]
  refine ⟨109250812145224699558005221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72833874763483133038670147 109250812145224699558005221)
  ·
    refine ⟨20484527277229631167125979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109250812145224699558005221 20484527277229631167125979)
    ·
      refine ⟨30726790915844446750688969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484527277229631167125979 30726790915844446750688969)
      ·
        refine ⟨23045093186883335063016727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30726790915844446750688969 23045093186883335063016727)
        ·
          refine ⟨34567639780325002594525091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23045093186883335063016727 34567639780325002594525091)
          ·
            refine ⟨51851459670487503891787637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34567639780325002594525091 51851459670487503891787637)
            ·
              refine ⟨4861074344108203489855091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51851459670487503891787637 4861074344108203489855091)
              ·
                refine ⟨7291611516162305234782637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4861074344108203489855091 7291611516162305234782637)
                ·
                  refine ⟨2734354318560864463043489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7291611516162305234782637 2734354318560864463043489)
                  ·
                    refine ⟨2050765738920648347282617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2734354318560864463043489 2050765738920648347282617)
                    ·
                      refine ⟨1538074304190486260461963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050765738920648347282617 1538074304190486260461963)
                      ·
                        rfl

theorem cell23_2995389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_2995389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995389 prefixEnd_2995389 := by exact prefixLift 2995389
  have htrace : WordTrace (prefixWord ++ tailWord_2995389) baseStart_2995389 baseEnd_2995389 := by
    simpa [prefixWord, tailWord_2995389, baseEnd_2995389] using wordTrace_append hprefix tailTrace_2995389
  have hstable : (prefixWord ++ tailWord_2995389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995389).length < 2 ^ (prefixWord ++ tailWord_2995389).sum := by decide
  have hdescent : baseEnd_2995389 < baseStart_2995389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995406 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_2995406 : Nat := 118140960795 + 2995406 * 2 ^ 59
def prefixEnd_2995406 : Nat := 4983230072969 + 3 ^ 40 * 2995406 * 2
def baseEnd_2995406 : Nat := 1538083033361612693949385

theorem tailTrace_2995406 : CollatzResearch.WordTrace tailWord_2995406 prefixEnd_2995406 1538083033361612693949385 := by
  unfold tailWord_2995406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13656429023270388932671759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72834288124108740974249381 13656429023270388932671759)
  ·
    refine ⟨20484643534905583399007639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13656429023270388932671759 20484643534905583399007639)
    ·
      refine ⟨30726965302358375098511459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484643534905583399007639 30726965302358375098511459)
      ·
        refine ⟨46090447953537562647767189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30726965302358375098511459 46090447953537562647767189)
        ·
          refine ⟨2160489747822073249114087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46090447953537562647767189 2160489747822073249114087)
          ·
            refine ⟨3240734621733109873671131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160489747822073249114087 3240734621733109873671131)
            ·
              refine ⟨4861101932599664810506697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240734621733109873671131 4861101932599664810506697)
              ·
                refine ⟨3645826449449748607880023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861101932599664810506697 3645826449449748607880023)
                ·
                  refine ⟨5468739674174622911820035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645826449449748607880023 5468739674174622911820035)
                  ·
                    refine ⟨8203109511261934367730053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5468739674174622911820035 8203109511261934367730053)
                    ·
                      refine ⟨1538083033361612693949385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8203109511261934367730053 1538083033361612693949385)
                      ·
                        rfl

theorem cell23_2995406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_2995406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995406 prefixEnd_2995406 := by exact prefixLift 2995406
  have htrace : WordTrace (prefixWord ++ tailWord_2995406) baseStart_2995406 baseEnd_2995406 := by
    simpa [prefixWord, tailWord_2995406, baseEnd_2995406] using wordTrace_append hprefix tailTrace_2995406
  have hstable : (prefixWord ++ tailWord_2995406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995406).length < 2 ^ (prefixWord ++ tailWord_2995406).sum := by decide
  have hdescent : baseEnd_2995406 < baseStart_2995406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995455 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 2, 6]
def baseStart_2995455 : Nat := 118140960795 + 2995455 * 2 ^ 59
def prefixEnd_2995455 : Nat := 4983230072969 + 3 ^ 40 * 2995455 * 2
def baseEnd_2995455 : Nat := 512702731304561000745553

theorem tailTrace_2995455 : CollatzResearch.WordTrace tailWord_2995455 prefixEnd_2995455 512702731304561000745553 := by
  unfold tailWord_2995455
  simp only [CollatzResearch.WordTrace]
  refine ⟨109253219362985592829907819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72835479575323728553271879 109253219362985592829907819)
  ·
    refine ⟨163879829044478389244861729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109253219362985592829907819 163879829044478389244861729)
    ·
      refine ⟨122909871783358791933646297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163879829044478389244861729 122909871783358791933646297)
      ·
        refine ⟨92182403837519093950234723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122909871783358791933646297 92182403837519093950234723)
        ·
          refine ⟨138273605756278640925352085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92182403837519093950234723 138273605756278640925352085)
          ·
            refine ⟨6481575269825561293375879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138273605756278640925352085 6481575269825561293375879)
            ·
              refine ⟨9722362904738341940063819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481575269825561293375879 9722362904738341940063819)
              ·
                refine ⟨14583544357107512910095729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9722362904738341940063819 14583544357107512910095729)
                ·
                  refine ⟨10937658267830634682571797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14583544357107512910095729 10937658267830634682571797)
                  ·
                    refine ⟨512702731304561000745553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10937658267830634682571797 512702731304561000745553)
                    ·
                      rfl

theorem cell23_2995455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_2995455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995455 prefixEnd_2995455 := by exact prefixLift 2995455
  have htrace : WordTrace (prefixWord ++ tailWord_2995455) baseStart_2995455 baseEnd_2995455 := by
    simpa [prefixWord, tailWord_2995455, baseEnd_2995455] using wordTrace_append hprefix tailTrace_2995455
  have hstable : (prefixWord ++ tailWord_2995455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995455).length < 2 ^ (prefixWord ++ tailWord_2995455).sum := by decide
  have hdescent : baseEnd_2995455 < baseStart_2995455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995465 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_2995465 : Nat := 118140960795 + 2995465 * 2 ^ 59
def prefixEnd_2995465 : Nat := 4983230072969 + 3 ^ 40 * 2995465 * 2
def baseEnd_2995465 : Nat := 1538113328720227963111613

theorem tailTrace_2995465 : CollatzResearch.WordTrace tailWord_2995465 prefixEnd_2995465 1538113328720227963111613 := by
  unfold tailWord_2995465
  simp only [CollatzResearch.WordTrace]
  refine ⟨109253584092949364537771849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72835722728632909691847899 109253584092949364537771849)
  ·
    refine ⟨81940188069712023403328887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109253584092949364537771849 81940188069712023403328887)
    ·
      refine ⟨122910282104568035104993331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81940188069712023403328887 122910282104568035104993331)
      ·
        refine ⟨184365423156852052657489997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122910282104568035104993331 184365423156852052657489997)
        ·
          refine ⟨69137033683819519746558749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184365423156852052657489997 69137033683819519746558749)
          ·
            refine ⟨25926387631432319904959531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69137033683819519746558749 25926387631432319904959531)
            ·
              refine ⟨38889581447148479857439297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25926387631432319904959531 38889581447148479857439297)
              ·
                refine ⟨29167186085361359893079473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38889581447148479857439297 29167186085361359893079473)
                ·
                  refine ⟨21875389564021019919809605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29167186085361359893079473 21875389564021019919809605)
                  ·
                    refine ⟨4101635543253941234964301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21875389564021019919809605 4101635543253941234964301)
                    ·
                      refine ⟨1538113328720227963111613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4101635543253941234964301 1538113328720227963111613)
                      ·
                        rfl

theorem cell23_2995465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_2995465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995465 prefixEnd_2995465 := by exact prefixLift 2995465
  have htrace : WordTrace (prefixWord ++ tailWord_2995465) baseStart_2995465 baseEnd_2995465 := by
    simpa [prefixWord, tailWord_2995465, baseEnd_2995465] using wordTrace_append hprefix tailTrace_2995465
  have hstable : (prefixWord ++ tailWord_2995465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995465).length < 2 ^ (prefixWord ++ tailWord_2995465).sum := by decide
  have hdescent : baseEnd_2995465 < baseStart_2995465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995479 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2995479 : Nat := 118140960795 + 2995479 * 2 ^ 59
def prefixEnd_2995479 : Nat := 4983230072969 + 3 ^ 40 * 2995479 * 2
def baseEnd_2995479 : Nat := 1538120517449390908336549

theorem tailTrace_2995479 : CollatzResearch.WordTrace tailWord_2995479 prefixEnd_2995479 1538120517449390908336549 := by
  unfold tailWord_2995479
  simp only [CollatzResearch.WordTrace]
  refine ⟨109254094714898644928781491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72836063143265763285854327 109254094714898644928781491)
  ·
    refine ⟨163881142072347967393172237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109254094714898644928781491 163881142072347967393172237)
    ·
      refine ⟨61455428277130487772439589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163881142072347967393172237 61455428277130487772439589)
      ·
        refine ⟨11522892801961966457332423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61455428277130487772439589 11522892801961966457332423)
        ·
          refine ⟨17284339202942949685998635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11522892801961966457332423 17284339202942949685998635)
          ·
            refine ⟨25926508804414424528997953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17284339202942949685998635 25926508804414424528997953)
            ·
              refine ⟨19444881603310818396748465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25926508804414424528997953 19444881603310818396748465)
              ·
                refine ⟨14583661202483113797561349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19444881603310818396748465 14583661202483113797561349)
                ·
                  refine ⟨2734436475465583837042753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14583661202483113797561349 2734436475465583837042753)
                  ·
                    refine ⟨2050827356599187877782065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2734436475465583837042753 2050827356599187877782065)
                    ·
                      refine ⟨1538120517449390908336549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050827356599187877782065 1538120517449390908336549)
                      ·
                        rfl

theorem cell23_2995479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2995479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995479 prefixEnd_2995479 := by exact prefixLift 2995479
  have htrace : WordTrace (prefixWord ++ tailWord_2995479) baseStart_2995479 baseEnd_2995479 := by
    simpa [prefixWord, tailWord_2995479, baseEnd_2995479] using wordTrace_append hprefix tailTrace_2995479
  have hstable : (prefixWord ++ tailWord_2995479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995479).length < 2 ^ (prefixWord ++ tailWord_2995479).sum := by decide
  have hdescent : baseEnd_2995479 < baseStart_2995479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995496 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_2995496 : Nat := 118140960795 + 2995496 * 2 ^ 59
def prefixEnd_2995496 : Nat := 4983230072969 + 3 ^ 40 * 2995496 * 2
def baseEnd_2995496 : Nat := 1538129246620517341823971

theorem tailTrace_2995496 : CollatzResearch.WordTrace tailWord_2995496 prefixEnd_2995496 1538129246620517341823971 := by
  unfold tailWord_2995496
  simp only [CollatzResearch.WordTrace]
  refine ⟨54627357377918528416075171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72836476503891371221433561 54627357377918528416075171)
  ·
    refine ⟨81941036066877792624112757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54627357377918528416075171 81941036066877792624112757)
    ·
      refine ⟨7681972131269793058510571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81941036066877792624112757 7681972131269793058510571)
      ·
        refine ⟨11522958196904689587765857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681972131269793058510571 11522958196904689587765857)
        ·
          refine ⟨8642218647678517190824393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11522958196904689587765857 8642218647678517190824393)
          ·
            refine ⟨6481663985758887893118295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8642218647678517190824393 6481663985758887893118295)
            ·
              refine ⟨9722495978638331839677443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481663985758887893118295 9722495978638331839677443)
              ·
                refine ⟨14583743967957497759516165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9722495978638331839677443 14583743967957497759516165)
                ·
                  refine ⟨2734451993992030829909281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14583743967957497759516165 2734451993992030829909281)
                  ·
                    refine ⟨2050838995494023122431961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2734451993992030829909281 2050838995494023122431961)
                    ·
                      refine ⟨1538129246620517341823971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050838995494023122431961 1538129246620517341823971)
                      ·
                        rfl

theorem cell23_2995496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_2995496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995496 prefixEnd_2995496 := by exact prefixLift 2995496
  have htrace : WordTrace (prefixWord ++ tailWord_2995496) baseStart_2995496 baseEnd_2995496 := by
    simpa [prefixWord, tailWord_2995496, baseEnd_2995496] using wordTrace_append hprefix tailTrace_2995496
  have hstable : (prefixWord ++ tailWord_2995496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995496).length < 2 ^ (prefixWord ++ tailWord_2995496).sum := by decide
  have hdescent : baseEnd_2995496 < baseStart_2995496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995513 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2995513 : Nat := 118140960795 + 2995513 * 2 ^ 59
def prefixEnd_2995513 : Nat := 4983230072969 + 3 ^ 40 * 2995513 * 2
def baseEnd_2995513 : Nat := 1538137975791643775311393

theorem tailTrace_2995513 : CollatzResearch.WordTrace tailWord_2995513 prefixEnd_2995513 1538137975791643775311393 := by
  unfold tailWord_2995513
  simp only [CollatzResearch.WordTrace]
  refine ⟨109255334796775468735519193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72836889864516979157012795 109255334796775468735519193)
  ·
    refine ⟨81941501097581601551639395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109255334796775468735519193 81941501097581601551639395)
    ·
      refine ⟨122912251646372402327459093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81941501097581601551639395 122912251646372402327459093)
      ·
        refine ⟨5761511795923706359099645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122912251646372402327459093 5761511795923706359099645)
        ·
          refine ⟨2160566923471389884662367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5761511795923706359099645 2160566923471389884662367)
          ·
            refine ⟨3240850385207084826993551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160566923471389884662367 3240850385207084826993551)
            ·
              refine ⟨4861275577810627240490327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240850385207084826993551 4861275577810627240490327)
              ·
                refine ⟨7291913366715940860735491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4861275577810627240490327 7291913366715940860735491)
                ·
                  refine ⟨10937870050073911291103237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7291913366715940860735491 10937870050073911291103237)
                  ·
                    refine ⟨2050850634388858367081857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10937870050073911291103237 2050850634388858367081857)
                    ·
                      refine ⟨1538137975791643775311393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2050850634388858367081857 1538137975791643775311393)
                      ·
                        rfl

theorem cell23_2995513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2995513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995513 prefixEnd_2995513 := by exact prefixLift 2995513
  have htrace : WordTrace (prefixWord ++ tailWord_2995513) baseStart_2995513 baseEnd_2995513 := by
    simpa [prefixWord, tailWord_2995513, baseEnd_2995513] using wordTrace_append hprefix tailTrace_2995513
  have hstable : (prefixWord ++ tailWord_2995513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995513).length < 2 ^ (prefixWord ++ tailWord_2995513).sum := by decide
  have hdescent : baseEnd_2995513 < baseStart_2995513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995552 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_2995552 : Nat := 118140960795 + 2995552 * 2 ^ 59
def prefixEnd_2995552 : Nat := 4983230072969 + 3 ^ 40 * 2995552 * 2
def baseEnd_2995552 : Nat := 1538158001537169122723713

theorem tailTrace_2995552 : CollatzResearch.WordTrace tailWord_2995552 prefixEnd_2995552 1538158001537169122723713 := by
  unfold tailWord_2995552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54628378621817089198094455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72837838162422785597459273 54628378621817089198094455)
  ·
    refine ⟨81942567932725633797141683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54628378621817089198094455 81942567932725633797141683)
    ·
      refine ⟨122913851899088450695712525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81942567932725633797141683 122913851899088450695712525)
      ·
        refine ⟨46092694462158169010892197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122913851899088450695712525 46092694462158169010892197)
        ·
          refine ⟨8642380211654656689542287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46092694462158169010892197 8642380211654656689542287)
          ·
            refine ⟨12963570317481985034313431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642380211654656689542287 12963570317481985034313431)
            ·
              refine ⟨19445355476222977551470147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963570317481985034313431 19445355476222977551470147)
              ·
                refine ⟨29168033214334466327205221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19445355476222977551470147 29168033214334466327205221)
                ·
                  refine ⟨5469006227687712436350979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29168033214334466327205221 5469006227687712436350979)
                  ·
                    refine ⟨8203509341531568654526469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469006227687712436350979 8203509341531568654526469)
                    ·
                      refine ⟨1538158001537169122723713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8203509341531568654526469 1538158001537169122723713)
                      ·
                        rfl

theorem cell23_2995552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_2995552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995552 prefixEnd_2995552 := by exact prefixLift 2995552
  have htrace : WordTrace (prefixWord ++ tailWord_2995552) baseStart_2995552 baseEnd_2995552 := by
    simpa [prefixWord, tailWord_2995552, baseEnd_2995552] using wordTrace_append hprefix tailTrace_2995552
  have hstable : (prefixWord ++ tailWord_2995552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995552).length < 2 ^ (prefixWord ++ tailWord_2995552).sum := by decide
  have hdescent : baseEnd_2995552 < baseStart_2995552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995586 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2995586 : Nat := 118140960795 + 2995586 * 2 ^ 59
def prefixEnd_2995586 : Nat := 4983230072969 + 3 ^ 40 * 2995586 * 2
def baseEnd_2995586 : Nat := 1538175459879421989698557

theorem tailTrace_2995586 : CollatzResearch.WordTrace tailWord_2995586 prefixEnd_2995586 1538175459879421989698557 := by
  unfold tailWord_2995586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314499331377750550731653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72838664883674001468617741 27314499331377750550731653)
  ·
    refine ⟨5121468624633328228262185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27314499331377750550731653 5121468624633328228262185)
    ·
      refine ⟨3841101468474996171196639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5121468624633328228262185 3841101468474996171196639)
      ·
        refine ⟨5761652202712494256794959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841101468474996171196639 5761652202712494256794959)
        ·
          refine ⟨8642478304068741385192439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761652202712494256794959 8642478304068741385192439)
          ·
            refine ⟨12963717456103112077788659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642478304068741385192439 12963717456103112077788659)
            ·
              refine ⟨19445576184154668116682989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963717456103112077788659 19445576184154668116682989)
              ·
                refine ⟨7292091069058000543756121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19445576184154668116682989 7292091069058000543756121)
                ·
                  refine ⟨5469068301793500407817091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7292091069058000543756121 5469068301793500407817091)
                  ·
                    refine ⟨8203602452690250611725637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469068301793500407817091 8203602452690250611725637)
                    ·
                      refine ⟨1538175459879421989698557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8203602452690250611725637 1538175459879421989698557)
                      ·
                        rfl

theorem cell23_2995586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2995586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995586 prefixEnd_2995586 := by exact prefixLift 2995586
  have htrace : WordTrace (prefixWord ++ tailWord_2995586) baseStart_2995586 baseEnd_2995586 := by
    simpa [prefixWord, tailWord_2995586, baseEnd_2995586] using wordTrace_append hprefix tailTrace_2995586
  have hstable : (prefixWord ++ tailWord_2995586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995586).length < 2 ^ (prefixWord ++ tailWord_2995586).sum := by decide
  have hdescent : baseEnd_2995586 < baseStart_2995586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995613 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2995613 : Nat := 118140960795 + 2995613 * 2 ^ 59
def prefixEnd_2995613 : Nat := 4983230072969 + 3 ^ 40 * 2995613 * 2
def baseEnd_2995613 : Nat := 512729774619031128020311

theorem tailTrace_2995613 : CollatzResearch.WordTrace tailWord_2995613 prefixEnd_2995613 512729774619031128020311 := by
  unfold tailWord_2995613
  simp only [CollatzResearch.WordTrace]
  refine ⟨109258982096413185814159493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72839321397608790542772995 109258982096413185814159493)
  ·
    refine ⟨20486059143077472340154905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109258982096413185814159493 20486059143077472340154905)
    ·
      refine ⟨15364544357308104255116179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20486059143077472340154905 15364544357308104255116179)
      ·
        refine ⟨23046816535962156382674269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15364544357308104255116179 23046816535962156382674269)
        ·
          refine ⟨8642556200985808643502851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23046816535962156382674269 8642556200985808643502851)
          ·
            refine ⟨12963834301478712965254277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642556200985808643502851 12963834301478712965254277)
            ·
              refine ⟨2430718931527258680985177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12963834301478712965254277 2430718931527258680985177)
              ·
                refine ⟨1823039198645444010738883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430718931527258680985177 1823039198645444010738883)
                ·
                  refine ⟨2734558797968166016108325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823039198645444010738883 2734558797968166016108325)
                  ·
                    refine ⟨512729774619031128020311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734558797968166016108325 512729774619031128020311)
                    ·
                      rfl

theorem cell23_2995613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2995613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995613 prefixEnd_2995613 := by exact prefixLift 2995613
  have htrace : WordTrace (prefixWord ++ tailWord_2995613) baseStart_2995613 baseEnd_2995613 := by
    simpa [prefixWord, tailWord_2995613, baseEnd_2995613] using wordTrace_append hprefix tailTrace_2995613
  have hstable : (prefixWord ++ tailWord_2995613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995613).length < 2 ^ (prefixWord ++ tailWord_2995613).sum := by decide
  have hdescent : baseEnd_2995613 < baseStart_2995613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995619 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 3]
def baseStart_2995619 : Nat := 118140960795 + 2995619 * 2 ^ 59
def prefixEnd_2995619 : Nat := 4983230072969 + 3 ^ 40 * 2995619 * 2
def baseEnd_2995619 : Nat := 1538192404741020360585905

theorem tailTrace_2995619 : CollatzResearch.WordTrace tailWord_2995619 prefixEnd_2995619 1538192404741020360585905 := by
  unfold tailWord_2995619
  simp only [CollatzResearch.WordTrace]
  refine ⟨109259200934391448838877911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72839467289594299225918607 109259200934391448838877911)
  ·
    refine ⟨163888801401587173258316867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109259200934391448838877911 163888801401587173258316867)
    ·
      refine ⟨245833202102380759887475301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163888801401587173258316867 245833202102380759887475301)
      ·
        refine ⟨46093725394196392478901619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245833202102380759887475301 46093725394196392478901619)
        ·
          refine ⟨69140588091294588718352429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46093725394196392478901619 69140588091294588718352429)
          ·
            refine ⟨25927720534235470769382161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69140588091294588718352429 25927720534235470769382161)
            ·
              refine ⟨19445790400676603077036621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25927720534235470769382161 19445790400676603077036621)
              ·
                refine ⟨7292171400253726153888733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19445790400676603077036621 7292171400253726153888733)
                ·
                  refine ⟨2734564275095147307708275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7292171400253726153888733 2734564275095147307708275)
                  ·
                    refine ⟨4101846412642720961562413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2734564275095147307708275 4101846412642720961562413)
                    ·
                      refine ⟨1538192404741020360585905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4101846412642720961562413 1538192404741020360585905)
                      ·
                        rfl

theorem cell23_2995619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_2995619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995619 prefixEnd_2995619 := by exact prefixLift 2995619
  have htrace : WordTrace (prefixWord ++ tailWord_2995619) baseStart_2995619 baseEnd_2995619 := by
    simpa [prefixWord, tailWord_2995619, baseEnd_2995619] using wordTrace_append hprefix tailTrace_2995619
  have hstable : (prefixWord ++ tailWord_2995619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995619).length < 2 ^ (prefixWord ++ tailWord_2995619).sum := by decide
  have hdescent : baseEnd_2995619 < baseStart_2995619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995669 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_2995669 : Nat := 118140960795 + 2995669 * 2 ^ 59
def prefixEnd_2995669 : Nat := 4983230072969 + 3 ^ 40 * 2995669 * 2
def baseEnd_2995669 : Nat := 512739359591248388320225

theorem tailTrace_2995669 : CollatzResearch.WordTrace tailWord_2995669 prefixEnd_2995669 512739359591248388320225 := by
  unfold tailWord_2995669
  simp only [CollatzResearch.WordTrace]
  refine ⟨109261024584210307378198061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72840683056140204918798707 109261024584210307378198061)
  ·
    refine ⟨40972884219078865266824273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109261024584210307378198061 40972884219078865266824273)
    ·
      refine ⟨30729663164309148950118205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40972884219078865266824273 30729663164309148950118205)
      ·
        refine ⟨11523623686615930856294327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30729663164309148950118205 11523623686615930856294327)
        ·
          refine ⟨17285435529923896284441491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523623686615930856294327 17285435529923896284441491)
          ·
            refine ⟨25928153294885844426662237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17285435529923896284441491 25928153294885844426662237)
            ·
              refine ⟨9723057485582191659998339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25928153294885844426662237 9723057485582191659998339)
              ·
                refine ⟨14584586228373287489997509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723057485582191659998339 14584586228373287489997509)
                ·
                  refine ⟨2734609917819991404374533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14584586228373287489997509 2734609917819991404374533)
                  ·
                    refine ⟨512739359591248388320225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2734609917819991404374533 512739359591248388320225)
                    ·
                      rfl

theorem cell23_2995669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_2995669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995669 prefixEnd_2995669 := by exact prefixLift 2995669
  have htrace : WordTrace (prefixWord ++ tailWord_2995669) baseStart_2995669 baseEnd_2995669 := by
    simpa [prefixWord, tailWord_2995669, baseEnd_2995669] using wordTrace_append hprefix tailTrace_2995669
  have hstable : (prefixWord ++ tailWord_2995669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995669).length < 2 ^ (prefixWord ++ tailWord_2995669).sum := by decide
  have hdescent : baseEnd_2995669 < baseStart_2995669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995670 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_2995670 : Nat := 118140960795 + 2995670 * 2 ^ 59
def prefixEnd_2995670 : Nat := 4983230072969 + 3 ^ 40 * 2995670 * 2
def baseEnd_2995670 : Nat := 1538218592254399661048171

theorem tailTrace_2995670 : CollatzResearch.WordTrace tailWord_2995670 prefixEnd_2995670 1538218592254399661048171 := by
  unfold tailWord_2995670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828816316075417784311529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72840707371471123032656309 6828816316075417784311529)
  ·
    refine ⟨5121612237056563338233647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6828816316075417784311529 5121612237056563338233647)
    ·
      refine ⟨7682418355584845007350471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121612237056563338233647 7682418355584845007350471)
      ·
        refine ⟨11523627533377267511025707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682418355584845007350471 11523627533377267511025707)
        ·
          refine ⟨17285441300065901266538561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523627533377267511025707 17285441300065901266538561)
          ·
            refine ⟨12964080975049425949903921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17285441300065901266538561 12964080975049425949903921)
            ·
              refine ⟨9723060731287069462427941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964080975049425949903921 9723060731287069462427941)
              ·
                refine ⟨1823073887116325524205239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9723060731287069462427941 1823073887116325524205239)
                ·
                  refine ⟨2734610830674488286307859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823073887116325524205239 2734610830674488286307859)
                  ·
                    refine ⟨4101916246011732429461789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2734610830674488286307859 4101916246011732429461789)
                    ·
                      refine ⟨1538218592254399661048171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4101916246011732429461789 1538218592254399661048171)
                      ·
                        rfl

theorem cell23_2995670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_2995670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995670 prefixEnd_2995670 := by exact prefixLift 2995670
  have htrace : WordTrace (prefixWord ++ tailWord_2995670) baseStart_2995670 baseEnd_2995670 := by
    simpa [prefixWord, tailWord_2995670, baseEnd_2995670] using wordTrace_append hprefix tailTrace_2995670
  have hstable : (prefixWord ++ tailWord_2995670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995670).length < 2 ^ (prefixWord ++ tailWord_2995670).sum := by decide
  have hdescent : baseEnd_2995670 < baseStart_2995670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995672 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2995672 : Nat := 118140960795 + 2995672 * 2 ^ 59
def prefixEnd_2995672 : Nat := 4983230072969 + 3 ^ 40 * 2995672 * 2
def baseEnd_2995672 : Nat := 1538219619215708653223161

theorem tailTrace_2995672 : CollatzResearch.WordTrace tailWord_2995672 prefixEnd_2995672 1538219619215708653223161 := by
  unfold tailWord_2995672
  simp only [CollatzResearch.WordTrace]
  refine ⟨54630567001599719445278635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72840756002132959260371513 54630567001599719445278635)
  ·
    refine ⟨81945850502399579167917953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54630567001599719445278635 81945850502399579167917953)
    ·
      refine ⟨61459387876799684375938465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81945850502399579167917953 61459387876799684375938465)
      ·
        refine ⟨46094540907599763281953849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61459387876799684375938465 46094540907599763281953849)
        ·
          refine ⟨34570905680699822461465387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46094540907599763281953849 34570905680699822461465387)
          ·
            refine ⟨51856358521049733692198081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34570905680699822461465387 51856358521049733692198081)
            ·
              refine ⟨38892268890787300269148561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51856358521049733692198081 38892268890787300269148561)
              ·
                refine ⟨29169201668090475201861421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38892268890787300269148561 29169201668090475201861421)
                ·
                  refine ⟨10938450625533928200698033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29169201668090475201861421 10938450625533928200698033)
                  ·
                    refine ⟨8203837969150446150523525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10938450625533928200698033 8203837969150446150523525)
                    ·
                      refine ⟨1538219619215708653223161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8203837969150446150523525 1538219619215708653223161)
                      ·
                        rfl

theorem cell23_2995672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2995672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995672 prefixEnd_2995672 := by exact prefixLift 2995672
  have htrace : WordTrace (prefixWord ++ tailWord_2995672) baseStart_2995672 baseEnd_2995672 := by
    simpa [prefixWord, tailWord_2995672, baseEnd_2995672] using wordTrace_append hprefix tailTrace_2995672
  have hstable : (prefixWord ++ tailWord_2995672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995672).length < 2 ^ (prefixWord ++ tailWord_2995672).sum := by decide
  have hdescent : baseEnd_2995672 < baseStart_2995672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995693 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2995693 : Nat := 118140960795 + 2995693 * 2 ^ 59
def prefixEnd_2995693 : Nat := 4983230072969 + 3 ^ 40 * 2995693 * 2
def baseEnd_2995693 : Nat := 1538230402309453071060565

theorem tailTrace_2995693 : CollatzResearch.WordTrace tailWord_2995693 prefixEnd_2995693 1538230402309453071060565 := by
  unfold tailWord_2995693
  simp only [CollatzResearch.WordTrace]
  refine ⟨109261899936123359477071733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72841266624082239651381155 109261899936123359477071733)
  ·
    refine ⟨10243303119011564950975475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109261899936123359477071733 10243303119011564950975475)
    ·
      refine ⟨15364954678517347426463213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10243303119011564950975475 15364954678517347426463213)
      ·
        refine ⟨5761858004444005284923705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15364954678517347426463213 5761858004444005284923705)
        ·
          refine ⟨4321393503333003963692779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5761858004444005284923705 4321393503333003963692779)
          ·
            refine ⟨6482090254999505945539169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321393503333003963692779 6482090254999505945539169)
            ·
              refine ⟨4861567691249629459154377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482090254999505945539169 4861567691249629459154377)
              ·
                refine ⟨3646175768437222094365783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861567691249629459154377 3646175768437222094365783)
                ·
                  refine ⟨5469263652655833141548675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646175768437222094365783 5469263652655833141548675)
                  ·
                    refine ⟨8203895478983749712323013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5469263652655833141548675 8203895478983749712323013)
                    ·
                      refine ⟨1538230402309453071060565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8203895478983749712323013 1538230402309453071060565)
                      ·
                        rfl

theorem cell23_2995693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2995693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995693 prefixEnd_2995693 := by exact prefixLift 2995693
  have htrace : WordTrace (prefixWord ++ tailWord_2995693) baseStart_2995693 baseEnd_2995693 := by
    simpa [prefixWord, tailWord_2995693, baseEnd_2995693] using wordTrace_append hprefix tailTrace_2995693
  have hstable : (prefixWord ++ tailWord_2995693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995693).length < 2 ^ (prefixWord ++ tailWord_2995693).sum := by decide
  have hdescent : baseEnd_2995693 < baseStart_2995693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995696 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3]
def baseStart_2995696 : Nat := 118140960795 + 2995696 * 2 ^ 59
def prefixEnd_2995696 : Nat := 4983230072969 + 3 ^ 40 * 2995696 * 2
def baseEnd_2995696 : Nat := 1538231942751416559323051

theorem tailTrace_2995696 : CollatzResearch.WordTrace tailWord_2995696 prefixEnd_2995696 1538231942751416559323051 := by
  unfold tailWord_2995696
  simp only [CollatzResearch.WordTrace]
  refine ⟨54631004677556245494715471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72841339570074993992953961 54631004677556245494715471)
  ·
    refine ⟨81946507016334368242073207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54631004677556245494715471 81946507016334368242073207)
    ·
      refine ⟨122919760524501552363109811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81946507016334368242073207 122919760524501552363109811)
      ·
        refine ⟨184379640786752328544664717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122919760524501552363109811 184379640786752328544664717)
        ·
          refine ⟨69142365295032123204249269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184379640786752328544664717 69142365295032123204249269)
          ·
            refine ⟨6482096746409261550398369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69142365295032123204249269 6482096746409261550398369)
            ·
              refine ⟨4861572559806946162798777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482096746409261550398369 4861572559806946162798777)
              ·
                refine ⟨3646179419855209622099083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861572559806946162798777 3646179419855209622099083)
                ·
                  refine ⟨5469269129782814433148625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646179419855209622099083 5469269129782814433148625)
                  ·
                    refine ⟨4101951847337110824861469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5469269129782814433148625 4101951847337110824861469)
                    ·
                      refine ⟨1538231942751416559323051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4101951847337110824861469 1538231942751416559323051)
                      ·
                        rfl

theorem cell23_2995696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_2995696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995696 prefixEnd_2995696 := by exact prefixLift 2995696
  have htrace : WordTrace (prefixWord ++ tailWord_2995696) baseStart_2995696 baseEnd_2995696 := by
    simpa [prefixWord, tailWord_2995696, baseEnd_2995696] using wordTrace_append hprefix tailTrace_2995696
  have hstable : (prefixWord ++ tailWord_2995696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995696).length < 2 ^ (prefixWord ++ tailWord_2995696).sum := by decide
  have hdescent : baseEnd_2995696 < baseStart_2995696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995716 : List Nat := [2, 3, 2, 3, 3, 1, 9]
def baseStart_2995716 : Nat := 118140960795 + 2995716 * 2 ^ 59
def prefixEnd_2995716 : Nat := 4983230072969 + 3 ^ 40 * 2995716 * 2
def baseEnd_2995716 : Nat := 18990644597092672605839

theorem tailTrace_2995716 : CollatzResearch.WordTrace tailWord_2995716 prefixEnd_2995716 18990644597092672605839 := by
  unfold tailWord_2995716
  simp only [CollatzResearch.WordTrace]
  refine ⟨54631369407520017202579501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72841825876693356270106001 54631369407520017202579501)
  ·
    refine ⟨20486763527820006450967313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54631369407520017202579501 20486763527820006450967313)
    ·
      refine ⟨15365072645865004838225485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20486763527820006450967313 15365072645865004838225485)
      ·
        refine ⟨5761902242199376814334557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15365072645865004838225485 5761902242199376814334557)
        ·
          refine ⟨2160713340824766305375459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5761902242199376814334557 2160713340824766305375459)
          ·
            refine ⟨3241070011237149458063189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160713340824766305375459 3241070011237149458063189)
            ·
              refine ⟨18990644597092672605839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3241070011237149458063189 18990644597092672605839)
              ·
                rfl

theorem cell23_2995716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 9].length) (baseStart_2995716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995716 prefixEnd_2995716 := by exact prefixLift 2995716
  have htrace : WordTrace (prefixWord ++ tailWord_2995716) baseStart_2995716 baseEnd_2995716 := by
    simpa [prefixWord, tailWord_2995716, baseEnd_2995716] using wordTrace_append hprefix tailTrace_2995716
  have hstable : (prefixWord ++ tailWord_2995716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995716).length < 2 ^ (prefixWord ++ tailWord_2995716).sum := by decide
  have hdescent : baseEnd_2995716 < baseStart_2995716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995743 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 2, 1, 3]
def baseStart_2995743 : Nat := 118140960795 + 2995743 * 2 ^ 59
def prefixEnd_2995743 : Nat := 4983230072969 + 3 ^ 40 * 2995743 * 2
def baseEnd_2995743 : Nat := 1538256076342177875435335

theorem tailTrace_2995743 : CollatzResearch.WordTrace tailWord_2995743 prefixEnd_2995743 1538256076342177875435335 := by
  unfold tailWord_2995743
  simp only [CollatzResearch.WordTrace]
  refine ⟨109263723585942218016391883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72842482390628145344261255 109263723585942218016391883)
  ·
    refine ⟨163895585378913327024587825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109263723585942218016391883 163895585378913327024587825)
    ·
      refine ⟨122921689034184995268440869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163895585378913327024587825 122921689034184995268440869)
      ·
        refine ⟨23047816693909686612832663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122921689034184995268440869 23047816693909686612832663)
        ·
          refine ⟨34571725040864529919248995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23047816693909686612832663 34571725040864529919248995)
          ·
            refine ⟨51857587561296794878873493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34571725040864529919248995 51857587561296794878873493)
            ·
              refine ⟨2430824416935787259947195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51857587561296794878873493 2430824416935787259947195)
              ·
                refine ⟨3646236625403680889920793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430824416935787259947195 3646236625403680889920793)
                ·
                  refine ⟨2734677469052760667440595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3646236625403680889920793 2734677469052760667440595)
                  ·
                    refine ⟨4102016203579141001160893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2734677469052760667440595 4102016203579141001160893)
                    ·
                      refine ⟨1538256076342177875435335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4102016203579141001160893 1538256076342177875435335)
                      ·
                        rfl

theorem cell23_2995743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_2995743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995743 prefixEnd_2995743 := by exact prefixLift 2995743
  have htrace : WordTrace (prefixWord ++ tailWord_2995743) baseStart_2995743 baseEnd_2995743 := by
    simpa [prefixWord, tailWord_2995743, baseEnd_2995743] using wordTrace_append hprefix tailTrace_2995743
  have hstable : (prefixWord ++ tailWord_2995743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995743).length < 2 ^ (prefixWord ++ tailWord_2995743).sum := by decide
  have hdescent : baseEnd_2995743 < baseStart_2995743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995769 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2995769 : Nat := 118140960795 + 2995769 * 2 ^ 59
def prefixEnd_2995769 : Nat := 4983230072969 + 3 ^ 40 * 2995769 * 2
def baseEnd_2995769 : Nat := 1538269426839194773710215

theorem tailTrace_2995769 : CollatzResearch.WordTrace tailWord_2995769 prefixEnd_2995769 1538269426839194773710215 := by
  unfold tailWord_2995769
  simp only [CollatzResearch.WordTrace]
  refine ⟨109264671883848024456838361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72843114589232016304558907 109264671883848024456838361)
  ·
    refine ⟨81948503912886018342628771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109264671883848024456838361 81948503912886018342628771)
    ·
      refine ⟨122922755869329027513943157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81948503912886018342628771 122922755869329027513943157)
      ·
        refine ⟨11524008362749596329432171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122922755869329027513943157 11524008362749596329432171)
        ·
          refine ⟨17286012544124394494148257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11524008362749596329432171 17286012544124394494148257)
          ·
            refine ⟨12964509408093295870611193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17286012544124394494148257 12964509408093295870611193)
            ·
              refine ⟨9723382056069971902958395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964509408093295870611193 9723382056069971902958395)
              ·
                refine ⟨14585073084104957854437593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723382056069971902958395 14585073084104957854437593)
                ·
                  refine ⟨10938804813078718390828195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14585073084104957854437593 10938804813078718390828195)
                  ·
                    refine ⟨16408207219618077586242293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10938804813078718390828195 16408207219618077586242293)
                    ·
                      refine ⟨1538269426839194773710215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16408207219618077586242293 1538269426839194773710215)
                      ·
                        rfl

theorem cell23_2995769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2995769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995769 prefixEnd_2995769 := by exact prefixLift 2995769
  have htrace : WordTrace (prefixWord ++ tailWord_2995769) baseStart_2995769 baseEnd_2995769 := by
    simpa [prefixWord, tailWord_2995769, baseEnd_2995769] using wordTrace_append hprefix tailTrace_2995769
  have hstable : (prefixWord ++ tailWord_2995769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995769).length < 2 ^ (prefixWord ++ tailWord_2995769).sum := by decide
  have hdescent : baseEnd_2995769 < baseStart_2995769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995799 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_2995799 : Nat := 118140960795 + 2995799 * 2 ^ 59
def prefixEnd_2995799 : Nat := 4983230072969 + 3 ^ 40 * 2995799 * 2
def baseEnd_2995799 : Nat := 1538284831258829656335077

theorem tailTrace_2995799 : CollatzResearch.WordTrace tailWord_2995799 prefixEnd_2995799 1538284831258829656335077 := by
  unfold tailWord_2995799
  simp only [CollatzResearch.WordTrace]
  refine ⟨109265766073739339580430451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72843844049159559720286967 109265766073739339580430451)
  ·
    refine ⟨163898649110609009370645677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109265766073739339580430451 163898649110609009370645677)
    ·
      refine ⟨61461993416478378513992129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163898649110609009370645677 61461993416478378513992129)
      ·
        refine ⟨46096495062358783885494097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61461993416478378513992129 46096495062358783885494097)
        ·
          refine ⟨34572371296769087914120573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46096495062358783885494097 34572371296769087914120573)
          ·
            refine ⟨12964639236288407967795215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34572371296769087914120573 12964639236288407967795215)
            ·
              refine ⟨19446958854432611951692823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964639236288407967795215 19446958854432611951692823)
              ·
                refine ⟨29170438281648917927539235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19446958854432611951692823 29170438281648917927539235)
                ·
                  refine ⟨43755657422473376891308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29170438281648917927539235 43755657422473376891308853)
                  ·
                    refine ⟨4102092883356879083560205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43755657422473376891308853 4102092883356879083560205)
                    ·
                      refine ⟨1538284831258829656335077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4102092883356879083560205 1538284831258829656335077)
                      ·
                        rfl

theorem cell23_2995799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_2995799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995799 prefixEnd_2995799 := by exact prefixLift 2995799
  have htrace : WordTrace (prefixWord ++ tailWord_2995799) baseStart_2995799 baseEnd_2995799 := by
    simpa [prefixWord, tailWord_2995799, baseEnd_2995799] using wordTrace_append hprefix tailTrace_2995799
  have hstable : (prefixWord ++ tailWord_2995799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995799).length < 2 ^ (prefixWord ++ tailWord_2995799).sum := by decide
  have hdescent : baseEnd_2995799 < baseStart_2995799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995869 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2995869 : Nat := 118140960795 + 2995869 * 2 ^ 59
def prefixEnd_2995869 : Nat := 4983230072969 + 3 ^ 40 * 2995869 * 2
def baseEnd_2995869 : Nat := 1538320774904644382459755

theorem tailTrace_2995869 : CollatzResearch.WordTrace tailWord_2995869 prefixEnd_2995869 1538320774904644382459755 := by
  unfold tailWord_2995869
  simp only [CollatzResearch.WordTrace]
  refine ⟨109268319183485741535478661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72845546122323827690319107 109268319183485741535478661)
  ·
    refine ⟨20487809846903576537902249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109268319183485741535478661 20487809846903576537902249)
    ·
      refine ⟨15365857385177682403426687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20487809846903576537902249 15365857385177682403426687)
      ·
        refine ⟨23048786077766523605140031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15365857385177682403426687 23048786077766523605140031)
        ·
          refine ⟨34573179116649785407710047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23048786077766523605140031 34573179116649785407710047)
          ·
            refine ⟨51859768674974678111565071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34573179116649785407710047 51859768674974678111565071)
            ·
              refine ⟨77789653012462017167347607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51859768674974678111565071 77789653012462017167347607)
              ·
                refine ⟨116684479518693025751021411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77789653012462017167347607 116684479518693025751021411)
                ·
                  refine ⟨175026719278039538626532117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116684479518693025751021411 175026719278039538626532117)
                  ·
                    refine ⟨8204377466158103373118693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175026719278039538626532117 8204377466158103373118693)
                    ·
                      refine ⟨1538320774904644382459755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8204377466158103373118693 1538320774904644382459755)
                      ·
                        rfl

theorem cell23_2995869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2995869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995869 prefixEnd_2995869 := by exact prefixLift 2995869
  have htrace : WordTrace (prefixWord ++ tailWord_2995869) baseStart_2995869 baseEnd_2995869 := by
    simpa [prefixWord, tailWord_2995869, baseEnd_2995869] using wordTrace_append hprefix tailTrace_2995869
  have hstable : (prefixWord ++ tailWord_2995869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995869).length < 2 ^ (prefixWord ++ tailWord_2995869).sum := by decide
  have hdescent : baseEnd_2995869 < baseStart_2995869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995876 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_2995876 : Nat := 118140960795 + 2995876 * 2 ^ 59
def prefixEnd_2995876 : Nat := 4983230072969 + 3 ^ 40 * 2995876 * 2
def baseEnd_2995876 : Nat := 1538324369269225855072223

theorem tailTrace_2995876 : CollatzResearch.WordTrace tailWord_2995876 prefixEnd_2995876 1538324369269225855072223 := by
  unfold tailWord_2995876
  simp only [CollatzResearch.WordTrace]
  refine ⟨54634287247230190865491741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72845716329640254487322321 54634287247230190865491741)
  ·
    refine ⟨20487857717711321574559403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54634287247230190865491741 20487857717711321574559403)
    ·
      refine ⟨30731786576566982361839105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20487857717711321574559403 30731786576566982361839105)
      ·
        refine ⟨23048839932425236771379329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30731786576566982361839105 23048839932425236771379329)
        ·
          refine ⟨17286629949318927578534497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23048839932425236771379329 17286629949318927578534497)
          ·
            refine ⟨12964972461989195683900873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17286629949318927578534497 12964972461989195683900873)
            ·
              refine ⟨9723729346491896762925655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964972461989195683900873 9723729346491896762925655)
              ·
                refine ⟨14585594019737845144388483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723729346491896762925655 14585594019737845144388483)
                ·
                  refine ⟨21878391029606767716582725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14585594019737845144388483 21878391029606767716582725)
                  ·
                    refine ⟨4102198318051268946859261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21878391029606767716582725 4102198318051268946859261)
                    ·
                      refine ⟨1538324369269225855072223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4102198318051268946859261 1538324369269225855072223)
                      ·
                        rfl

theorem cell23_2995876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_2995876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995876 prefixEnd_2995876 := by exact prefixLift 2995876
  have htrace : WordTrace (prefixWord ++ tailWord_2995876) baseStart_2995876 baseEnd_2995876 := by
    simpa [prefixWord, tailWord_2995876, baseEnd_2995876] using wordTrace_append hprefix tailTrace_2995876
  have hstable : (prefixWord ++ tailWord_2995876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995876).length < 2 ^ (prefixWord ++ tailWord_2995876).sum := by decide
  have hdescent : baseEnd_2995876 < baseStart_2995876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995909 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_2995909 : Nat := 118140960795 + 2995909 * 2 ^ 59
def prefixEnd_2995909 : Nat := 4983230072969 + 3 ^ 40 * 2995909 * 2
def baseEnd_2995909 : Nat := 512780438043608075319857

theorem tailTrace_2995909 : CollatzResearch.WordTrace tailWord_2995909 prefixEnd_2995909 512780438043608075319857 := by
  unfold tailWord_2995909
  simp only [CollatzResearch.WordTrace]
  refine ⟨109269778103340828366934781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72846518735560552244623187 109269778103340828366934781)
  ·
    refine ⟨40976166788752810637600543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109269778103340828366934781 40976166788752810637600543)
    ·
      refine ⟨61464250183129215956400815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40976166788752810637600543 61464250183129215956400815)
      ·
        refine ⟨92196375274693823934601223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61464250183129215956400815 92196375274693823934601223)
        ·
          refine ⟨138294562912040735901901835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92196375274693823934601223 138294562912040735901901835)
          ·
            refine ⟨207441844368061103852852753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138294562912040735901901835 207441844368061103852852753)
            ·
              refine ⟨155581383276045827889639565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207441844368061103852852753 155581383276045827889639565)
              ·
                refine ⟨58343018728517185458614837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155581383276045827889639565 58343018728517185458614837)
                ·
                  refine ⟨5469658005798486136745141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58343018728517185458614837 5469658005798486136745141)
                  ·
                    refine ⟨512780438043608075319857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5469658005798486136745141 512780438043608075319857)
                    ·
                      rfl

theorem cell23_2995909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_2995909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995909 prefixEnd_2995909 := by exact prefixLift 2995909
  have htrace : WordTrace (prefixWord ++ tailWord_2995909) baseStart_2995909 baseEnd_2995909 := by
    simpa [prefixWord, tailWord_2995909, baseEnd_2995909] using wordTrace_append hprefix tailTrace_2995909
  have hstable : (prefixWord ++ tailWord_2995909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995909).length < 2 ^ (prefixWord ++ tailWord_2995909).sum := by decide
  have hdescent : baseEnd_2995909 < baseStart_2995909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995940 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_2995940 : Nat := 118140960795 + 2995940 * 2 ^ 59
def prefixEnd_2995940 : Nat := 4983230072969 + 3 ^ 40 * 2995940 * 2
def baseEnd_2995940 : Nat := 1538357232031113604671929

theorem tailTrace_2995940 : CollatzResearch.WordTrace tailWord_2995940 prefixEnd_2995940 1538357232031113604671929 := by
  unfold tailWord_2995940
  simp only [CollatzResearch.WordTrace]
  refine ⟨54635454383114260330656637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72847272510819013774208849 54635454383114260330656637)
  ·
    refine ⟨20488295393667847623996239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54635454383114260330656637 20488295393667847623996239)
    ·
      refine ⟨30732443090501771435994359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20488295393667847623996239 30732443090501771435994359)
      ·
        refine ⟨46098664635752657153991539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30732443090501771435994359 46098664635752657153991539)
        ·
          refine ⟨69147996953628985730987309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46098664635752657153991539 69147996953628985730987309)
          ·
            refine ⟨25930498857610869649120241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69147996953628985730987309 25930498857610869649120241)
            ·
              refine ⟨19447874143208152236840181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25930498857610869649120241 19447874143208152236840181)
              ·
                refine ⟨1823238200925764272203767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19447874143208152236840181 1823238200925764272203767)
                ·
                  refine ⟨2734857301388646408305651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823238200925764272203767 2734857301388646408305651)
                  ·
                    refine ⟨4102285952082969612458477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2734857301388646408305651 4102285952082969612458477)
                    ·
                      refine ⟨1538357232031113604671929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4102285952082969612458477 1538357232031113604671929)
                      ·
                        rfl

theorem cell23_2995940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_2995940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995940 prefixEnd_2995940 := by exact prefixLift 2995940
  have htrace : WordTrace (prefixWord ++ tailWord_2995940) baseStart_2995940 baseEnd_2995940 := by
    simpa [prefixWord, tailWord_2995940, baseEnd_2995940] using wordTrace_append hprefix tailTrace_2995940
  have hstable : (prefixWord ++ tailWord_2995940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995940).length < 2 ^ (prefixWord ++ tailWord_2995940).sum := by decide
  have hdescent : baseEnd_2995940 < baseStart_2995940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995959 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_2995959 : Nat := 118140960795 + 2995959 * 2 ^ 59
def prefixEnd_2995959 : Nat := 4983230072969 + 3 ^ 40 * 2995959 * 2
def baseEnd_2995959 : Nat := 1538366988163549030334341

theorem tailTrace_2995959 : CollatzResearch.WordTrace tailWord_2995959 prefixEnd_2995959 1538366988163549030334341 := by
  unfold tailWord_2995959
  simp only [CollatzResearch.WordTrace]
  refine ⟨109271601753159686906254931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72847734502106457937503287 109271601753159686906254931)
  ·
    refine ⟨163907402629739530359382397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109271601753159686906254931 163907402629739530359382397)
    ·
      refine ⟨61465275986152323884768399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163907402629739530359382397 61465275986152323884768399)
      ·
        refine ⟨92197913979228485827152599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61465275986152323884768399 92197913979228485827152599)
        ·
          refine ⟨138296870968842728740728899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92197913979228485827152599 138296870968842728740728899)
          ·
            refine ⟨207445306453264093111093349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138296870968842728740728899 207445306453264093111093349)
            ·
              refine ⟨38895994959987017458330003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207445306453264093111093349 38895994959987017458330003)
              ·
                refine ⟨58343992439980526187495005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38895994959987017458330003 58343992439980526187495005)
                ·
                  refine ⟨21878997164992697320310627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58343992439980526187495005 21878997164992697320310627)
                  ·
                    refine ⟨32818495747489045980465941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21878997164992697320310627 32818495747489045980465941)
                    ·
                      refine ⟨1538366988163549030334341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32818495747489045980465941 1538366988163549030334341)
                      ·
                        rfl

theorem cell23_2995959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_2995959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2995959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2995959 prefixEnd_2995959 := by exact prefixLift 2995959
  have htrace : WordTrace (prefixWord ++ tailWord_2995959) baseStart_2995959 baseEnd_2995959 := by
    simpa [prefixWord, tailWord_2995959, baseEnd_2995959] using wordTrace_append hprefix tailTrace_2995959
  have hstable : (prefixWord ++ tailWord_2995959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995959).length < 2 ^ (prefixWord ++ tailWord_2995959).sum := by decide
  have hdescent : baseEnd_2995959 < baseStart_2995959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996009 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_2996009 : Nat := 118140960795 + 2996009 * 2 ^ 59
def prefixEnd_2996009 : Nat := 4983230072969 + 3 ^ 40 * 2996009 * 2
def baseEnd_2996009 : Nat := 1538392662196273834709111

theorem tailTrace_2996009 : CollatzResearch.WordTrace tailWord_2996009 prefixEnd_2996009 1538392662196273834709111 := by
  unfold tailWord_2996009
  simp only [CollatzResearch.WordTrace]
  refine ⟨109273425402978545445575081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72848950268652363630383387 109273425402978545445575081)
  ·
    refine ⟨81955069052233909084181311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109273425402978545445575081 81955069052233909084181311)
    ·
      refine ⟨122932603578350863626271967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81955069052233909084181311 122932603578350863626271967)
      ·
        refine ⟨184398905367526295439407951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122932603578350863626271967 184398905367526295439407951)
        ·
          refine ⟨276598358051289443159111927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184398905367526295439407951 276598358051289443159111927)
          ·
            refine ⟨414897537076934164738667891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276598358051289443159111927 414897537076934164738667891)
            ·
              refine ⟨622346305615401247108001837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414897537076934164738667891 622346305615401247108001837)
              ·
                refine ⟨233379864605775467665500689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622346305615401247108001837 233379864605775467665500689)
                ·
                  refine ⟨175034898454331600749125517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233379864605775467665500689 175034898454331600749125517)
                  ·
                    refine ⟨65638086920374350280922069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175034898454331600749125517 65638086920374350280922069)
                    ·
                      refine ⟨1538392662196273834709111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65638086920374350280922069 1538392662196273834709111)
                      ·
                        rfl

theorem cell23_2996009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_2996009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996009 prefixEnd_2996009 := by exact prefixLift 2996009
  have htrace : WordTrace (prefixWord ++ tailWord_2996009) baseStart_2996009 baseEnd_2996009 := by
    simpa [prefixWord, tailWord_2996009, baseEnd_2996009] using wordTrace_append hprefix tailTrace_2996009
  have hstable : (prefixWord ++ tailWord_2996009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996009).length < 2 ^ (prefixWord ++ tailWord_2996009).sum := by decide
  have hdescent : baseEnd_2996009 < baseStart_2996009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996014 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2996014 : Nat := 118140960795 + 2996014 * 2 ^ 59
def prefixEnd_2996014 : Nat := 4983230072969 + 3 ^ 40 * 2996014 * 2
def baseEnd_2996014 : Nat := 1538395229599546315146589

theorem tailTrace_2996014 : CollatzResearch.WordTrace tailWord_2996014 prefixEnd_2996014 1538395229599546315146589 := by
  unfold tailWord_2996014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659200970995053912438387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72849071845306954199671397 13659200970995053912438387)
  ·
    refine ⟨20488801456492580868657581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13659200970995053912438387 20488801456492580868657581)
    ·
      refine ⟨7683300546184717825746593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20488801456492580868657581 7683300546184717825746593)
      ·
        refine ⟨5762475409638538369309945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683300546184717825746593 5762475409638538369309945)
        ·
          refine ⟨4321856557228903776982459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5762475409638538369309945 4321856557228903776982459)
          ·
            refine ⟨6482784835843355665473689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321856557228903776982459 6482784835843355665473689)
            ·
              refine ⟨4862088626882516749105267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482784835843355665473689 4862088626882516749105267)
              ·
                refine ⟨7293132940323775123657901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862088626882516749105267 7293132940323775123657901)
                ·
                  refine ⟨2734924852621415671371713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7293132940323775123657901 2734924852621415671371713)
                  ·
                    refine ⟨2051193639466061753528785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2734924852621415671371713 2051193639466061753528785)
                    ·
                      refine ⟨1538395229599546315146589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051193639466061753528785 1538395229599546315146589)
                      ·
                        rfl

theorem cell23_2996014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2996014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996014 prefixEnd_2996014 := by exact prefixLift 2996014
  have htrace : WordTrace (prefixWord ++ tailWord_2996014) baseStart_2996014 baseEnd_2996014 := by
    simpa [prefixWord, tailWord_2996014, baseEnd_2996014] using wordTrace_append hprefix tailTrace_2996014
  have hstable : (prefixWord ++ tailWord_2996014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996014).length < 2 ^ (prefixWord ++ tailWord_2996014).sum := by decide
  have hdescent : baseEnd_2996014 < baseStart_2996014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996023 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 3, 3, 2]
def baseStart_2996023 : Nat := 118140960795 + 2996023 * 2 ^ 59
def prefixEnd_2996023 : Nat := 4983230072969 + 3 ^ 40 * 2996023 * 2
def baseEnd_2996023 : Nat := 1538399850925436779934047

theorem tailTrace_2996023 : CollatzResearch.WordTrace tailWord_2996023 prefixEnd_2996023 1538399850925436779934047 := by
  unfold tailWord_2996023
  simp only [CollatzResearch.WordTrace]
  refine ⟨109273936024927825836584723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72849290683285217224389815 109273936024927825836584723)
  ·
    refine ⟨163910904037391738754877085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109273936024927825836584723 163910904037391738754877085)
    ·
      refine ⟨61466589014021902033078907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163910904037391738754877085 61466589014021902033078907)
      ·
        refine ⟨92199883521032853049618361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61466589014021902033078907 92199883521032853049618361)
        ·
          refine ⟨69149912640774639787213771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92199883521032853049618361 69149912640774639787213771)
          ·
            refine ⟨103724868961161959680820657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69149912640774639787213771 103724868961161959680820657)
            ·
              refine ⟨77793651720871469760615493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103724868961161959680820657 77793651720871469760615493)
              ·
                refine ⟨14586309697663400580115405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77793651720871469760615493 14586309697663400580115405)
                ·
                  refine ⟨5469866136623775217543277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14586309697663400580115405 5469866136623775217543277)
                  ·
                    refine ⟨2051199801233915706578729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5469866136623775217543277 2051199801233915706578729)
                    ·
                      refine ⟨1538399850925436779934047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051199801233915706578729 1538399850925436779934047)
                      ·
                        rfl

theorem cell23_2996023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_2996023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996023 prefixEnd_2996023 := by exact prefixLift 2996023
  have htrace : WordTrace (prefixWord ++ tailWord_2996023) baseStart_2996023 baseEnd_2996023 := by
    simpa [prefixWord, tailWord_2996023, baseEnd_2996023] using wordTrace_append hprefix tailTrace_2996023
  have hstable : (prefixWord ++ tailWord_2996023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996023).length < 2 ^ (prefixWord ++ tailWord_2996023).sum := by decide
  have hdescent : baseEnd_2996023 < baseStart_2996023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996030 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2996030 : Nat := 118140960795 + 2996030 * 2 ^ 59
def prefixEnd_2996030 : Nat := 4983230072969 + 3 ^ 40 * 2996030 * 2
def baseEnd_2996030 : Nat := 1538403445290018252546515

theorem tailTrace_2996030 : CollatzResearch.WordTrace tailWord_2996030 prefixEnd_2996030 1538403445290018252546515 := by
  unfold tailWord_2996030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659273916987808254011193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72849460890601644021393029 13659273916987808254011193)
  ·
    refine ⟨10244455437740856190508395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13659273916987808254011193 10244455437740856190508395)
    ·
      refine ⟨15366683156611284285762593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10244455437740856190508395 15366683156611284285762593)
      ·
        refine ⟨11525012367458463214321945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15366683156611284285762593 11525012367458463214321945)
        ·
          refine ⟨8643759275593847410741459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11525012367458463214321945 8643759275593847410741459)
          ·
            refine ⟨12965638913390771116112189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643759275593847410741459 12965638913390771116112189)
            ·
              refine ⟨4862114592521539168542071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12965638913390771116112189 4862114592521539168542071)
              ·
                refine ⟨7293171888782308752813107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862114592521539168542071 7293171888782308752813107)
                ·
                  refine ⟨10939757833173463129219661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7293171888782308752813107 10939757833173463129219661)
                  ·
                    refine ⟨4102409187440048673457373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10939757833173463129219661 4102409187440048673457373)
                    ·
                      refine ⟨1538403445290018252546515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4102409187440048673457373 1538403445290018252546515)
                      ·
                        rfl

theorem cell23_2996030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2996030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996030 prefixEnd_2996030 := by exact prefixLift 2996030
  have htrace : WordTrace (prefixWord ++ tailWord_2996030) baseStart_2996030 baseEnd_2996030 := by
    simpa [prefixWord, tailWord_2996030, baseEnd_2996030] using wordTrace_append hprefix tailTrace_2996030
  have hstable : (prefixWord ++ tailWord_2996030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996030).length < 2 ^ (prefixWord ++ tailWord_2996030).sum := by decide
  have hdescent : baseEnd_2996030 < baseStart_2996030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996040 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_2996040 : Nat := 118140960795 + 2996040 * 2 ^ 59
def prefixEnd_2996040 : Nat := 4983230072969 + 3 ^ 40 * 2996040 * 2
def baseEnd_2996040 : Nat := 1538408580096563213421469

theorem tailTrace_2996040 : CollatzResearch.WordTrace tailWord_2996040 prefixEnd_2996040 1538408580096563213421469 := by
  unfold tailWord_2996040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54637278032933118869976787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72849704043910825159969049 54637278032933118869976787)
  ·
    refine ⟨81955917049399678304965181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54637278032933118869976787 81955917049399678304965181)
    ·
      refine ⟨30733468893524879364361943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81955917049399678304965181 30733468893524879364361943)
      ·
        refine ⟨46100203340287319046542915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30733468893524879364361943 46100203340287319046542915)
        ·
          refine ⟨69150305010430978569814373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46100203340287319046542915 69150305010430978569814373)
          ·
            refine ⟨12965682189455808481840195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69150305010430978569814373 12965682189455808481840195)
            ·
              refine ⟨19448523284183712722760293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12965682189455808481840195 19448523284183712722760293)
              ·
                refine ⟨3646598115784446135517555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19448523284183712722760293 3646598115784446135517555)
                ·
                  refine ⟨5469897173676669203276333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646598115784446135517555 5469897173676669203276333)
                  ·
                    refine ⟨2051211440128750951228625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5469897173676669203276333 2051211440128750951228625)
                    ·
                      refine ⟨1538408580096563213421469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051211440128750951228625 1538408580096563213421469)
                      ·
                        rfl

theorem cell23_2996040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_2996040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996040 prefixEnd_2996040 := by exact prefixLift 2996040
  have htrace : WordTrace (prefixWord ++ tailWord_2996040) baseStart_2996040 baseEnd_2996040 := by
    simpa [prefixWord, tailWord_2996040, baseEnd_2996040] using wordTrace_append hprefix tailTrace_2996040
  have hstable : (prefixWord ++ tailWord_2996040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996040).length < 2 ^ (prefixWord ++ tailWord_2996040).sum := by decide
  have hdescent : baseEnd_2996040 < baseStart_2996040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996056 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_2996056 : Nat := 118140960795 + 2996056 * 2 ^ 59
def prefixEnd_2996056 : Nat := 4983230072969 + 3 ^ 40 * 2996056 * 2
def baseEnd_2996056 : Nat := 1538416795787035150821395

theorem tailTrace_2996056 : CollatzResearch.WordTrace tailWord_2996056 prefixEnd_2996056 1538416795787035150821395 := by
  unfold tailWord_2996056
  simp only [CollatzResearch.WordTrace]
  refine ⟨54637569816904136236268011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72850093089205514981690681 54637569816904136236268011)
  ·
    refine ⟨81956354725356204354402017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54637569816904136236268011 81956354725356204354402017)
    ·
      refine ⟨61467266044017153265801513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81956354725356204354402017 61467266044017153265801513)
      ·
        refine ⟨46100449533012864949351135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61467266044017153265801513 46100449533012864949351135)
        ·
          refine ⟨69150674299519297424026703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46100449533012864949351135 69150674299519297424026703)
          ·
            refine ⟨103726011449278946136040055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69150674299519297424026703 103726011449278946136040055)
            ·
              refine ⟨155589017173918419204060083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103726011449278946136040055 155589017173918419204060083)
              ·
                refine ⟨233383525760877628806090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155589017173918419204060083 233383525760877628806090125)
                ·
                  refine ⟨87518822160329110802283797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233383525760877628806090125 87518822160329110802283797)
                  ·
                    refine ⟨4102444788765427068857053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87518822160329110802283797 4102444788765427068857053)
                    ·
                      refine ⟨1538416795787035150821395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4102444788765427068857053 1538416795787035150821395)
                      ·
                        rfl

theorem cell23_2996056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_2996056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996056 prefixEnd_2996056 := by exact prefixLift 2996056
  have htrace : WordTrace (prefixWord ++ tailWord_2996056) baseStart_2996056 baseEnd_2996056 := by
    simpa [prefixWord, tailWord_2996056, baseEnd_2996056] using wordTrace_append hprefix tailTrace_2996056
  have hstable : (prefixWord ++ tailWord_2996056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996056).length < 2 ^ (prefixWord ++ tailWord_2996056).sum := by decide
  have hdescent : baseEnd_2996056 < baseStart_2996056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996180 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2996180 : Nat := 118140960795 + 2996180 * 2 ^ 59
def prefixEnd_2996180 : Nat := 4983230072969 + 3 ^ 40 * 2996180 * 2
def baseEnd_2996180 : Nat := 1538480467388192665670825

theorem tailTrace_2996180 : CollatzResearch.WordTrace tailWord_2996180 prefixEnd_2996180 1538480467388192665670825 := by
  unfold tailWord_2996180
  simp only [CollatzResearch.WordTrace]
  refine ⟨54639831142679520825024997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72853108190239361100033329 54639831142679520825024997)
  ·
    refine ⟨10244968339252410154692187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54639831142679520825024997 10244968339252410154692187)
    ·
      refine ⟨15367452508878615232038281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10244968339252410154692187 15367452508878615232038281)
      ·
        refine ⟨11525589381658961424028711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15367452508878615232038281 11525589381658961424028711)
        ·
          refine ⟨17288384072488442136043067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11525589381658961424028711 17288384072488442136043067)
          ·
            refine ⟨25932576108732663204064601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17288384072488442136043067 25932576108732663204064601)
            ·
              refine ⟨19449432081549497403048451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25932576108732663204064601 19449432081549497403048451)
              ·
                refine ⟨29174148122324246104572677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19449432081549497403048451 29174148122324246104572677)
                ·
                  refine ⟨5470152772935796144607377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29174148122324246104572677 5470152772935796144607377)
                  ·
                    refine ⟨4102614579701847108455533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470152772935796144607377 4102614579701847108455533)
                    ·
                      refine ⟨1538480467388192665670825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4102614579701847108455533 1538480467388192665670825)
                      ·
                        rfl

theorem cell23_2996180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2996180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996180 prefixEnd_2996180 := by exact prefixLift 2996180
  have htrace : WordTrace (prefixWord ++ tailWord_2996180) baseStart_2996180 baseEnd_2996180 := by
    simpa [prefixWord, tailWord_2996180, baseEnd_2996180] using wordTrace_append hprefix tailTrace_2996180
  have hstable : (prefixWord ++ tailWord_2996180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996180).length < 2 ^ (prefixWord ++ tailWord_2996180).sum := by decide
  have hdescent : baseEnd_2996180 < baseStart_2996180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996220 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_2996220 : Nat := 118140960795 + 2996220 * 2 ^ 59
def prefixEnd_2996220 : Nat := 4983230072969 + 3 ^ 40 * 2996220 * 2
def baseEnd_2996220 : Nat := 1538501006614372509170641

theorem tailTrace_2996220 : CollatzResearch.WordTrace tailWord_2996220 prefixEnd_2996220 1538501006614372509170641 := by
  unfold tailWord_2996220
  simp only [CollatzResearch.WordTrace]
  refine ⟨54640560602607064240753057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72854080803476085654337409 54640560602607064240753057)
  ·
    refine ⟨40980420451955298180564793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54640560602607064240753057 40980420451955298180564793)
    ·
      refine ⟨30735315338966473635423595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40980420451955298180564793 30735315338966473635423595)
      ·
        refine ⟨46102973008449710453135393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30735315338966473635423595 46102973008449710453135393)
        ·
          refine ⟨34577229756337282839851545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46102973008449710453135393 34577229756337282839851545)
          ·
            refine ⟨25932922317252962129888659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34577229756337282839851545 25932922317252962129888659)
            ·
              refine ⟨38899383475879443194832989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25932922317252962129888659 38899383475879443194832989)
              ·
                refine ⟨14587268803454791198062371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38899383475879443194832989 14587268803454791198062371)
                ·
                  refine ⟨21880903205182186797093557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14587268803454791198062371 21880903205182186797093557)
                  ·
                    refine ⟨2051334675485830012227521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21880903205182186797093557 2051334675485830012227521)
                    ·
                      refine ⟨1538501006614372509170641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051334675485830012227521 1538501006614372509170641)
                      ·
                        rfl

theorem cell23_2996220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_2996220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996220 prefixEnd_2996220 := by exact prefixLift 2996220
  have htrace : WordTrace (prefixWord ++ tailWord_2996220) baseStart_2996220 baseEnd_2996220 := by
    simpa [prefixWord, tailWord_2996220, baseEnd_2996220] using wordTrace_append hprefix tailTrace_2996220
  have hstable : (prefixWord ++ tailWord_2996220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996220).length < 2 ^ (prefixWord ++ tailWord_2996220).sum := by decide
  have hdescent : baseEnd_2996220 < baseStart_2996220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996233 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_2996233 : Nat := 118140960795 + 2996233 * 2 ^ 59
def prefixEnd_2996233 : Nat := 4983230072969 + 3 ^ 40 * 2996233 * 2
def baseEnd_2996233 : Nat := 1538507681862880958308081

theorem tailTrace_2996233 : CollatzResearch.WordTrace tailWord_2996233 prefixEnd_2996233 1538507681862880958308081 := by
  unfold tailWord_2996233
  simp only [CollatzResearch.WordTrace]
  refine ⟨109281595354167031701729353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72854396902778021134486235 109281595354167031701729353)
  ·
    refine ⟨81961196515625273776297015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109281595354167031701729353 81961196515625273776297015)
    ·
      refine ⟨122941794773437910664445523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81961196515625273776297015 122941794773437910664445523)
      ·
        refine ⟨184412692160156865996668285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122941794773437910664445523 184412692160156865996668285)
        ·
          refine ⟨69154759560058824748750607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184412692160156865996668285 69154759560058824748750607)
          ·
            refine ⟨103732139340088237123125911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69154759560058824748750607 103732139340088237123125911)
            ·
              refine ⟨155598209010132355684688867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103732139340088237123125911 155598209010132355684688867)
              ·
                refine ⟨233397313515198533527033301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155598209010132355684688867 233397313515198533527033301)
                ·
                  refine ⟨5470249535512465629539843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 233397313515198533527033301 5470249535512465629539843)
                  ·
                    refine ⟨8205374303268698444309765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5470249535512465629539843 8205374303268698444309765)
                    ·
                      refine ⟨1538507681862880958308081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8205374303268698444309765 1538507681862880958308081)
                      ·
                        rfl

theorem cell23_2996233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_2996233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996233 prefixEnd_2996233 := by exact prefixLift 2996233
  have htrace : WordTrace (prefixWord ++ tailWord_2996233) baseStart_2996233 baseEnd_2996233 := by
    simpa [prefixWord, tailWord_2996233, baseEnd_2996233] using wordTrace_append hprefix tailTrace_2996233
  have hstable : (prefixWord ++ tailWord_2996233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996233).length < 2 ^ (prefixWord ++ tailWord_2996233).sum := by decide
  have hdescent : baseEnd_2996233 < baseStart_2996233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996273 : List Nat := [1, 2, 2, 3, 1, 3, 2, 9]
def baseStart_2996273 : Nat := 118140960795 + 2996273 * 2 ^ 59
def prefixEnd_2996273 : Nat := 4983230072969 + 3 ^ 40 * 2996273 * 2
def baseEnd_2996273 : Nat := 56982526707002251918811

theorem tailTrace_2996273 : CollatzResearch.WordTrace tailWord_2996273 prefixEnd_2996273 56982526707002251918811 := by
  unfold tailWord_2996273
  simp only [CollatzResearch.WordTrace]
  refine ⟨109283054274022118533185473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72855369516014745688790315 109283054274022118533185473)
  ·
    refine ⟨81962290705516588899889105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109283054274022118533185473 81962290705516588899889105)
    ·
      refine ⟨61471718029137441674916829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81962290705516588899889105 61471718029137441674916829)
      ·
        refine ⟨23051894260926540628093811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61471718029137441674916829 23051894260926540628093811)
        ·
          refine ⟨34577841391389810942140717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23051894260926540628093811 34577841391389810942140717)
          ·
            refine ⟨12966690521771179103302769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34577841391389810942140717 12966690521771179103302769)
            ·
              refine ⟨9725017891328384327477077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12966690521771179103302769 9725017891328384327477077)
              ·
                refine ⟨56982526707002251918811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9725017891328384327477077 56982526707002251918811)
                ·
                  rfl

theorem cell23_2996273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 9].length) (baseStart_2996273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996273 prefixEnd_2996273 := by exact prefixLift 2996273
  have htrace : WordTrace (prefixWord ++ tailWord_2996273) baseStart_2996273 baseEnd_2996273 := by
    simpa [prefixWord, tailWord_2996273, baseEnd_2996273] using wordTrace_append hprefix tailTrace_2996273
  have hstable : (prefixWord ++ tailWord_2996273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996273).length < 2 ^ (prefixWord ++ tailWord_2996273).sum := by decide
  have hdescent : baseEnd_2996273 < baseStart_2996273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996327 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_2996327 : Nat := 118140960795 + 2996327 * 2 ^ 59
def prefixEnd_2996327 : Nat := 4983230072969 + 3 ^ 40 * 2996327 * 2
def baseEnd_2996327 : Nat := 1538555949044403590532649

theorem tailTrace_2996327 : CollatzResearch.WordTrace tailWord_2996327 prefixEnd_2996327 1538555949044403590532649 := by
  unfold tailWord_2996327
  simp only [CollatzResearch.WordTrace]
  refine ⟨109285023815826485755651235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72856682543884323837100823 109285023815826485755651235)
  ·
    refine ⟨163927535723739728633476853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109285023815826485755651235 163927535723739728633476853)
    ·
      refine ⟨15368206474100599559388455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163927535723739728633476853 15368206474100599559388455)
      ·
        refine ⟨23052309711150899339082683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15368206474100599559388455 23052309711150899339082683)
        ·
          refine ⟨34578464566726349008624025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23052309711150899339082683 34578464566726349008624025)
          ·
            refine ⟨25933848425044761756468019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34578464566726349008624025 25933848425044761756468019)
            ·
              refine ⟨38900772637567142634702029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25933848425044761756468019 38900772637567142634702029)
              ·
                refine ⟨14587789739087678488013261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38900772637567142634702029 14587789739087678488013261)
                ·
                  refine ⟨5470421152157879433004973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14587789739087678488013261 5470421152157879433004973)
                  ·
                    refine ⟨2051407932059204787376865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5470421152157879433004973 2051407932059204787376865)
                    ·
                      refine ⟨1538555949044403590532649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051407932059204787376865 1538555949044403590532649)
                      ·
                        rfl

theorem cell23_2996327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_2996327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996327 prefixEnd_2996327 := by exact prefixLift 2996327
  have htrace : WordTrace (prefixWord ++ tailWord_2996327) baseStart_2996327 baseEnd_2996327 := by
    simpa [prefixWord, tailWord_2996327, baseEnd_2996327] using wordTrace_append hprefix tailTrace_2996327
  have hstable : (prefixWord ++ tailWord_2996327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996327).length < 2 ^ (prefixWord ++ tailWord_2996327).sum := by decide
  have hdescent : baseEnd_2996327 < baseStart_2996327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996380 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 7]
def baseStart_2996380 : Nat := 118140960795 + 2996380 * 2 ^ 59
def prefixEnd_2996380 : Nat := 4983230072969 + 3 ^ 40 * 2996380 * 2
def baseEnd_2996380 : Nat := 170953684835454653685545

theorem tailTrace_2996380 : CollatzResearch.WordTrace tailWord_2996380 prefixEnd_2996380 170953684835454653685545 := by
  unfold tailWord_2996380
  simp only [CollatzResearch.WordTrace]
  refine ⟨54643478442317237903665297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72857971256422983871553729 54643478442317237903665297)
  ·
    refine ⟨40982608831737928427748973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54643478442317237903665297 40982608831737928427748973)
    ·
      refine ⟨15368478311901723160405865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40982608831737928427748973 15368478311901723160405865)
      ·
        refine ⟨11526358733926292370304399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15368478311901723160405865 11526358733926292370304399)
        ·
          refine ⟨17289538100889438555456599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11526358733926292370304399 17289538100889438555456599)
          ·
            refine ⟨25934307151334157833184899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17289538100889438555456599 25934307151334157833184899)
            ·
              refine ⟨38901460727001236749777349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25934307151334157833184899 38901460727001236749777349)
              ·
                refine ⟨7294023886312731890583253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38901460727001236749777349 7294023886312731890583253)
                ·
                  refine ⟨170953684835454653685545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7294023886312731890583253 170953684835454653685545)
                  ·
                    rfl

theorem cell23_2996380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_2996380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996380 prefixEnd_2996380 := by exact prefixLift 2996380
  have htrace : WordTrace (prefixWord ++ tailWord_2996380) baseStart_2996380 baseEnd_2996380 := by
    simpa [prefixWord, tailWord_2996380, baseEnd_2996380] using wordTrace_append hprefix tailTrace_2996380
  have hstable : (prefixWord ++ tailWord_2996380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996380).length < 2 ^ (prefixWord ++ tailWord_2996380).sum := by decide
  have hdescent : baseEnd_2996380 < baseStart_2996380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996394 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2996394 : Nat := 118140960795 + 2996394 * 2 ^ 59
def prefixEnd_2996394 : Nat := 4983230072969 + 3 ^ 40 * 2996394 * 2
def baseEnd_2996394 : Nat := 1538590352248254828394841

theorem tailTrace_2996394 : CollatzResearch.WordTrace tailWord_2996394 prefixEnd_2996394 1538590352248254828394841 := by
  unfold tailWord_2996394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27321866876645939049585059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72858311671055837465560157 27321866876645939049585059)
  ·
    refine ⟨40982800314968908574377589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27321866876645939049585059 40982800314968908574377589)
    ·
      refine ⟨3842137529528335178847899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40982800314968908574377589 3842137529528335178847899)
      ·
        refine ⟨5763206294292502768271849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842137529528335178847899 5763206294292502768271849)
        ·
          refine ⟨4322404720719377076203887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5763206294292502768271849 4322404720719377076203887)
          ·
            refine ⟨6483607081079065614305831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4322404720719377076203887 6483607081079065614305831)
            ·
              refine ⟨9725410621618598421458747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6483607081079065614305831 9725410621618598421458747)
              ·
                refine ⟨14588115932427897632188121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9725410621618598421458747 14588115932427897632188121)
                ·
                  refine ⟨10941086949320923224141091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14588115932427897632188121 10941086949320923224141091)
                  ·
                    refine ⟨16411630423981384836211637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10941086949320923224141091 16411630423981384836211637)
                    ·
                      refine ⟨1538590352248254828394841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16411630423981384836211637 1538590352248254828394841)
                      ·
                        rfl

theorem cell23_2996394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2996394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996394 prefixEnd_2996394 := by exact prefixLift 2996394
  have htrace : WordTrace (prefixWord ++ tailWord_2996394) baseStart_2996394 baseEnd_2996394 := by
    simpa [prefixWord, tailWord_2996394, baseEnd_2996394] using wordTrace_append hprefix tailTrace_2996394
  have hstable : (prefixWord ++ tailWord_2996394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996394).length < 2 ^ (prefixWord ++ tailWord_2996394).sum := by decide
  have hdescent : baseEnd_2996394 < baseStart_2996394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996410 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_2996410 : Nat := 118140960795 + 2996410 * 2 ^ 59
def prefixEnd_2996410 : Nat := 4983230072969 + 3 ^ 40 * 2996410 * 2
def baseEnd_2996410 : Nat := 512866189312908921931589

theorem tailTrace_2996410 : CollatzResearch.WordTrace tailWord_2996410 prefixEnd_2996410 512866189312908921931589 := by
  unfold tailWord_2996410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27322012768631447732730671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72858700716350527287281789 27322012768631447732730671)
  ·
    refine ⟨40983019152947171599096007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27322012768631447732730671 40983019152947171599096007)
    ·
      refine ⟨61474528729420757398644011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40983019152947171599096007 61474528729420757398644011)
      ·
        refine ⟨92211793094131136097966017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61474528729420757398644011 92211793094131136097966017)
        ·
          refine ⟨69158844820598352073474513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92211793094131136097966017 69158844820598352073474513)
          ·
            refine ⟨51869133615448764055105885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69158844820598352073474513 51869133615448764055105885)
            ·
              refine ⟨19450925105793286520664707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51869133615448764055105885 19450925105793286520664707)
              ·
                refine ⟨29176387658689929780997061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19450925105793286520664707 29176387658689929780997061)
                ·
                  refine ⟨5470572686004361833936949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29176387658689929780997061 5470572686004361833936949)
                  ·
                    refine ⟨512866189312908921931589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5470572686004361833936949 512866189312908921931589)
                    ·
                      rfl

theorem cell23_2996410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_2996410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996410 prefixEnd_2996410 := by exact prefixLift 2996410
  have htrace : WordTrace (prefixWord ++ tailWord_2996410) baseStart_2996410 baseEnd_2996410 := by
    simpa [prefixWord, tailWord_2996410, baseEnd_2996410] using wordTrace_append hprefix tailTrace_2996410
  have hstable : (prefixWord ++ tailWord_2996410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996410).length < 2 ^ (prefixWord ++ tailWord_2996410).sum := by decide
  have hdescent : baseEnd_2996410 < baseStart_2996410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996414 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2996414 : Nat := 118140960795 + 2996414 * 2 ^ 59
def prefixEnd_2996414 : Nat := 4983230072969 + 3 ^ 40 * 2996414 * 2
def baseEnd_2996414 : Nat := 170955624651260527793861

theorem tailTrace_2996414 : CollatzResearch.WordTrace tailWord_2996414 prefixEnd_2996414 170955624651260527793861 := by
  unfold tailWord_2996414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13661024620813912451758537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72858797977674199742712197 13661024620813912451758537)
  ·
    refine ⟨10245768465610434338818903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13661024620813912451758537 10245768465610434338818903)
    ·
      refine ⟨15368652698415651508228355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10245768465610434338818903 15368652698415651508228355)
      ·
        refine ⟨23052979047623477262342533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15368652698415651508228355 23052979047623477262342533)
        ·
          refine ⟨4322433571429401986689225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23052979047623477262342533 4322433571429401986689225)
          ·
            refine ⟨3241825178572051490016919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322433571429401986689225 3241825178572051490016919)
            ·
              refine ⟨4862737767858077235025379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241825178572051490016919 4862737767858077235025379)
              ·
                refine ⟨7294106651787115852538069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862737767858077235025379 7294106651787115852538069)
                ·
                  refine ⟨170955624651260527793861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7294106651787115852538069 170955624651260527793861)
                  ·
                    rfl

theorem cell23_2996414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2996414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996414 prefixEnd_2996414 := by exact prefixLift 2996414
  have htrace : WordTrace (prefixWord ++ tailWord_2996414) baseStart_2996414 baseEnd_2996414 := by
    simpa [prefixWord, tailWord_2996414, baseEnd_2996414] using wordTrace_append hprefix tailTrace_2996414
  have hstable : (prefixWord ++ tailWord_2996414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996414).length < 2 ^ (prefixWord ++ tailWord_2996414).sum := by decide
  have hdescent : baseEnd_2996414 < baseStart_2996414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996447 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 4, 4, 2]
def baseStart_2996447 : Nat := 118140960795 + 2996447 * 2 ^ 59
def prefixEnd_2996447 : Nat := 4983230072969 + 3 ^ 40 * 2996447 * 2
def baseEnd_2996447 : Nat := 1538617566722943121032097

theorem tailTrace_2996447 : CollatzResearch.WordTrace tailWord_2996447 prefixEnd_2996447 1538617566722943121032097 := by
  unfold tailWord_2996447
  simp only [CollatzResearch.WordTrace]
  refine ⟨109289400575391746250019595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72859600383594497500013063 109289400575391746250019595)
  ·
    refine ⟨163934100863087619375029393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109289400575391746250019595 163934100863087619375029393)
    ·
      refine ⟨122950575647315714531272045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163934100863087619375029393 122950575647315714531272045)
      ·
        refine ⟨46106465867743392949227017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122950575647315714531272045 46106465867743392949227017)
        ·
          refine ⟨34579849400807544711920263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46106465867743392949227017 34579849400807544711920263)
          ·
            refine ⟨51869774101211317067880395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34579849400807544711920263 51869774101211317067880395)
            ·
              refine ⟨77804661151816975601820593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51869774101211317067880395 77804661151816975601820593)
              ·
                refine ⟨58353495863862731701365445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77804661151816975601820593 58353495863862731701365445)
                ·
                  refine ⟨10941280474474262194006021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58353495863862731701365445 10941280474474262194006021)
                  ·
                    refine ⟨2051490088963924161376129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10941280474474262194006021 2051490088963924161376129)
                    ·
                      refine ⟨1538617566722943121032097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051490088963924161376129 1538617566722943121032097)
                      ·
                        rfl

theorem cell23_2996447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_2996447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996447 prefixEnd_2996447 := by exact prefixLift 2996447
  have htrace : WordTrace (prefixWord ++ tailWord_2996447) baseStart_2996447 baseEnd_2996447 := by
    simpa [prefixWord, tailWord_2996447, baseEnd_2996447] using wordTrace_append hprefix tailTrace_2996447
  have hstable : (prefixWord ++ tailWord_2996447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996447).length < 2 ^ (prefixWord ++ tailWord_2996447).sum := by decide
  have hdescent : baseEnd_2996447 < baseStart_2996447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996460 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_2996460 : Nat := 118140960795 + 2996460 * 2 ^ 59
def prefixEnd_2996460 : Nat := 4983230072969 + 3 ^ 40 * 2996460 * 2
def baseEnd_2996460 : Nat := 1538624241971451570169537

theorem tailTrace_2996460 : CollatzResearch.WordTrace tailWord_2996460 prefixEnd_2996460 1538624241971451570169537 := by
  unfold tailWord_2996460
  simp only [CollatzResearch.WordTrace]
  refine ⟨54644937362172324735121417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72859916482896432980161889 54644937362172324735121417)
  ·
    refine ⟨40983703021629243551341063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54644937362172324735121417 40983703021629243551341063)
    ·
      refine ⟨61475554532443865327011595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40983703021629243551341063 61475554532443865327011595)
      ·
        refine ⟨92213331798665797990517393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61475554532443865327011595 92213331798665797990517393)
        ·
          refine ⟨69159998848999348492888045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92213331798665797990517393 69159998848999348492888045)
          ·
            refine ⟨25934999568374755684833017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69159998848999348492888045 25934999568374755684833017)
            ·
              refine ⟨19451249676281066763624763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25934999568374755684833017 19451249676281066763624763)
              ·
                refine ⟨29176874514421600145437145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19451249676281066763624763 29176874514421600145437145)
                ·
                  refine ⟨21882655885816200109077859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29176874514421600145437145 21882655885816200109077859)
                  ·
                    refine ⟨32823983828724300163616789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21882655885816200109077859 32823983828724300163616789)
                    ·
                      refine ⟨1538624241971451570169537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32823983828724300163616789 1538624241971451570169537)
                      ·
                        rfl

theorem cell23_2996460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_2996460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996460 prefixEnd_2996460 := by exact prefixLift 2996460
  have htrace : WordTrace (prefixWord ++ tailWord_2996460) baseStart_2996460 baseEnd_2996460 := by
    simpa [prefixWord, tailWord_2996460, baseEnd_2996460] using wordTrace_append hprefix tailTrace_2996460
  have hstable : (prefixWord ++ tailWord_2996460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996460).length < 2 ^ (prefixWord ++ tailWord_2996460).sum := by decide
  have hdescent : baseEnd_2996460 < baseStart_2996460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996467 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 3]
def baseStart_2996467 : Nat := 118140960795 + 2996467 * 2 ^ 59
def prefixEnd_2996467 : Nat := 4983230072969 + 3 ^ 40 * 2996467 * 2
def baseEnd_2996467 : Nat := 1538627836336033042782005

theorem tailTrace_2996467 : CollatzResearch.WordTrace tailWord_2996467 prefixEnd_2996467 1538627836336033042782005 := by
  unfold tailWord_2996467
  simp only [CollatzResearch.WordTrace]
  refine ⟨109290130035319289665747655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72860086690212859777165103 109290130035319289665747655)
  ·
    refine ⟨163935195052978934498621483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109290130035319289665747655 163935195052978934498621483)
    ·
      refine ⟨245902792579468401747932225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163935195052978934498621483 245902792579468401747932225)
      ·
        refine ⟨184427094434601301310949169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245902792579468401747932225 184427094434601301310949169)
        ·
          refine ⟨138320320825950975983211877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184427094434601301310949169 138320320825950975983211877)
          ·
            refine ⟨25935060154865807996852227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138320320825950975983211877 25935060154865807996852227)
            ·
              refine ⟨38902590232298711995278341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25935060154865807996852227 38902590232298711995278341)
              ·
                refine ⟨7294235668556008499114689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38902590232298711995278341 7294235668556008499114689)
                ·
                  refine ⟨5470676751417006374336017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294235668556008499114689 5470676751417006374336017)
                  ·
                    refine ⟨4103007563562754780752013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5470676751417006374336017 4103007563562754780752013)
                    ·
                      refine ⟨1538627836336033042782005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103007563562754780752013 1538627836336033042782005)
                      ·
                        rfl

theorem cell23_2996467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_2996467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996467 prefixEnd_2996467 := by exact prefixLift 2996467
  have htrace : WordTrace (prefixWord ++ tailWord_2996467) baseStart_2996467 baseEnd_2996467 := by
    simpa [prefixWord, tailWord_2996467, baseEnd_2996467] using wordTrace_append hprefix tailTrace_2996467
  have hstable : (prefixWord ++ tailWord_2996467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996467).length < 2 ^ (prefixWord ++ tailWord_2996467).sum := by decide
  have hdescent : baseEnd_2996467 < baseStart_2996467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996524 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 2, 3, 2]
def baseStart_2996524 : Nat := 118140960795 + 2996524 * 2 ^ 59
def prefixEnd_2996524 : Nat := 4983230072969 + 3 ^ 40 * 2996524 * 2
def baseEnd_2996524 : Nat := 1538657104733339319769243

theorem tailTrace_2996524 : CollatzResearch.WordTrace tailWord_2996524 prefixEnd_2996524 1538657104733339319769243 := by
  unfold tailWord_2996524
  simp only [CollatzResearch.WordTrace]
  refine ⟨54646104498056394200286313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72861472664075192267048417 54646104498056394200286313)
  ·
    refine ⟨40984578373542295650214735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54646104498056394200286313 40984578373542295650214735)
    ·
      refine ⟨61476867560313443475322103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40984578373542295650214735 61476867560313443475322103)
      ·
        refine ⟨92215301340470165212983155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61476867560313443475322103 92215301340470165212983155)
        ·
          refine ⟨138322952010705247819474733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92215301340470165212983155 138322952010705247819474733)
          ·
            refine ⟨51871107004014467932303025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138322952010705247819474733 51871107004014467932303025)
            ·
              refine ⟨38903330253010850949227269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51871107004014467932303025 38903330253010850949227269)
              ·
                refine ⟨7294374422439534552980113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38903330253010850949227269 7294374422439534552980113)
                ·
                  refine ⟨5470780816829650914735085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294374422439534552980113 5470780816829650914735085)
                  ·
                    refine ⟨2051542806311119093025657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5470780816829650914735085 2051542806311119093025657)
                    ·
                      refine ⟨1538657104733339319769243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051542806311119093025657 1538657104733339319769243)
                      ·
                        rfl

theorem cell23_2996524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_2996524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996524 prefixEnd_2996524 := by exact prefixLift 2996524
  have htrace : WordTrace (prefixWord ++ tailWord_2996524) baseStart_2996524 baseEnd_2996524 := by
    simpa [prefixWord, tailWord_2996524, baseEnd_2996524] using wordTrace_append hprefix tailTrace_2996524
  have hstable : (prefixWord ++ tailWord_2996524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996524).length < 2 ^ (prefixWord ++ tailWord_2996524).sum := by decide
  have hdescent : baseEnd_2996524 < baseStart_2996524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996531 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 1, 1, 3]
def baseStart_2996531 : Nat := 118140960795 + 2996531 * 2 ^ 59
def prefixEnd_2996531 : Nat := 4983230072969 + 3 ^ 40 * 2996531 * 2
def baseEnd_2996531 : Nat := 1538660699097920792381711

theorem tailTrace_2996531 : CollatzResearch.WordTrace tailWord_2996531 prefixEnd_2996531 1538660699097920792381711 := by
  unfold tailWord_2996531
  simp only [CollatzResearch.WordTrace]
  refine ⟨109292464307087428596077447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72861642871391619064051631 109292464307087428596077447)
  ·
    refine ⟨163938696460631142894116171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109292464307087428596077447 163938696460631142894116171)
    ·
      refine ⟨245908044690946714341174257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163938696460631142894116171 245908044690946714341174257)
      ·
        refine ⟨184431033518210035755880693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245908044690946714341174257 184431033518210035755880693)
        ·
          refine ⟨17290409392332190852113815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184431033518210035755880693 17290409392332190852113815)
          ·
            refine ⟨25935614088498286278170723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17290409392332190852113815 25935614088498286278170723)
            ·
              refine ⟨38903421132747429417256085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25935614088498286278170723 38903421132747429417256085)
              ·
                refine ⟨1823597865597535753933879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38903421132747429417256085 1823597865597535753933879)
                ·
                  refine ⟨2735396798396303630900819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823597865597535753933879 2735396798396303630900819)
                  ·
                    refine ⟨4103095197594455446351229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735396798396303630900819 4103095197594455446351229)
                    ·
                      refine ⟨1538660699097920792381711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103095197594455446351229 1538660699097920792381711)
                      ·
                        rfl

theorem cell23_2996531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 1, 3].length) (baseStart_2996531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996531 prefixEnd_2996531 := by exact prefixLift 2996531
  have htrace : WordTrace (prefixWord ++ tailWord_2996531) baseStart_2996531 baseEnd_2996531 := by
    simpa [prefixWord, tailWord_2996531, baseEnd_2996531] using wordTrace_append hprefix tailTrace_2996531
  have hstable : (prefixWord ++ tailWord_2996531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996531).length < 2 ^ (prefixWord ++ tailWord_2996531).sum := by decide
  have hdescent : baseEnd_2996531 < baseStart_2996531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996547 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 1, 6]
def baseStart_2996547 : Nat := 118140960795 + 2996547 * 2 ^ 59
def prefixEnd_2996547 : Nat := 4983230072969 + 3 ^ 40 * 2996547 * 2
def baseEnd_2996547 : Nat := 512889638262797576593879

theorem tailTrace_2996547 : CollatzResearch.WordTrace tailWord_2996547 prefixEnd_2996547 512889638262797576593879 := by
  unfold tailWord_2996547
  simp only [CollatzResearch.WordTrace]
  refine ⟨109293047875029463328659895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72862031916686308885773263 109293047875029463328659895)
  ·
    refine ⟨163939571812544194992989843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109293047875029463328659895 163939571812544194992989843)
    ·
      refine ⟨245909357718816292489484765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163939571812544194992989843 245909357718816292489484765)
      ·
        refine ⟨92216009144556109683556787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245909357718816292489484765 92216009144556109683556787)
        ·
          refine ⟨138324013716834164525335181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92216009144556109683556787 138324013716834164525335181)
          ·
            refine ⟨51871505143812811697000693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138324013716834164525335181 51871505143812811697000693)
            ·
              refine ⟨4862953607232451096593815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51871505143812811697000693 4862953607232451096593815)
              ·
                refine ⟨7294430410848676644890723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862953607232451096593815 7294430410848676644890723)
                ·
                  refine ⟨10941645616273014967336085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7294430410848676644890723 10941645616273014967336085)
                  ·
                    refine ⟨512889638262797576593879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10941645616273014967336085 512889638262797576593879)
                    ·
                      rfl

theorem cell23_2996547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 6].length) (baseStart_2996547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996547 prefixEnd_2996547 := by exact prefixLift 2996547
  have htrace : WordTrace (prefixWord ++ tailWord_2996547) baseStart_2996547 baseEnd_2996547 := by
    simpa [prefixWord, tailWord_2996547, baseEnd_2996547] using wordTrace_append hprefix tailTrace_2996547
  have hstable : (prefixWord ++ tailWord_2996547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996547).length < 2 ^ (prefixWord ++ tailWord_2996547).sum := by decide
  have hdescent : baseEnd_2996547 < baseStart_2996547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996564 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_2996564 : Nat := 118140960795 + 2996564 * 2 ^ 59
def prefixEnd_2996564 : Nat := 4983230072969 + 3 ^ 40 * 2996564 * 2
def baseEnd_2996564 : Nat := 512892547986506387756353

theorem tailTrace_2996564 : CollatzResearch.WordTrace tailWord_2996564 prefixEnd_2996564 512892547986506387756353 := by
  unfold tailWord_2996564
  simp only [CollatzResearch.WordTrace]
  refine ⟨54646833957983937616014373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72862445277311916821352497 54646833957983937616014373)
  ·
    refine ⟨10246281367121988303002695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54646833957983937616014373 10246281367121988303002695)
    ·
      refine ⟨15369422050682982454504043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10246281367121988303002695 15369422050682982454504043)
      ·
        refine ⟨23054133076024473681756065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15369422050682982454504043 23054133076024473681756065)
        ·
          refine ⟨17290599807018355261317049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23054133076024473681756065 17290599807018355261317049)
          ·
            refine ⟨12967949855263766445987787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17290599807018355261317049 12967949855263766445987787)
            ·
              refine ⟨19451924782895649668981681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12967949855263766445987787 19451924782895649668981681)
              ·
                refine ⟨14588943587171737251736261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19451924782895649668981681 14588943587171737251736261)
                ·
                  refine ⟨2735426922594700734700549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14588943587171737251736261 2735426922594700734700549)
                  ·
                    refine ⟨512892547986506387756353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2735426922594700734700549 512892547986506387756353)
                    ·
                      rfl

theorem cell23_2996564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_2996564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996564 prefixEnd_2996564 := by exact prefixLift 2996564
  have htrace : WordTrace (prefixWord ++ tailWord_2996564) baseStart_2996564 baseEnd_2996564 := by
    simpa [prefixWord, tailWord_2996564, baseEnd_2996564] using wordTrace_append hprefix tailTrace_2996564
  have hstable : (prefixWord ++ tailWord_2996564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996564).length < 2 ^ (prefixWord ++ tailWord_2996564).sum := by decide
  have hdescent : baseEnd_2996564 < baseStart_2996564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996565 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2996565 : Nat := 118140960795 + 2996565 * 2 ^ 59
def prefixEnd_2996565 : Nat := 4983230072969 + 3 ^ 40 * 2996565 * 2
def baseEnd_2996565 : Nat := 1538678157440173659356555

theorem tailTrace_2996565 : CollatzResearch.WordTrace tailWord_2996565 prefixEnd_2996565 1538678157440173659356555 := by
  unfold tailWord_2996565
  simp only [CollatzResearch.WordTrace]
  refine ⟨109293704388964252402815149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72862469592642834935210099 109293704388964252402815149)
  ·
    refine ⟨40985139145861594651055681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109293704388964252402815149 40985139145861594651055681)
    ·
      refine ⟨30738854359396195988291761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40985139145861594651055681 30738854359396195988291761)
      ·
        refine ⟨23054140769547146991218821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30738854359396195988291761 23054140769547146991218821)
        ·
          refine ⟨4322651394290090060853529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23054140769547146991218821 4322651394290090060853529)
          ·
            refine ⟨3241988545717567545640147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322651394290090060853529 3241988545717567545640147)
            ·
              refine ⟨4862982818576351318460221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241988545717567545640147 4862982818576351318460221)
              ·
                refine ⟨1823618556966131744422583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4862982818576351318460221 1823618556966131744422583)
                ·
                  refine ⟨2735427835449197616633875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823618556966131744422583 2735427835449197616633875)
                  ·
                    refine ⟨4103141753173796424950813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735427835449197616633875 4103141753173796424950813)
                    ·
                      refine ⟨1538678157440173659356555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103141753173796424950813 1538678157440173659356555)
                      ·
                        rfl

theorem cell23_2996565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2996565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996565 prefixEnd_2996565 := by exact prefixLift 2996565
  have htrace : WordTrace (prefixWord ++ tailWord_2996565) baseStart_2996565 baseEnd_2996565 := by
    simpa [prefixWord, tailWord_2996565, baseEnd_2996565] using wordTrace_append hprefix tailTrace_2996565
  have hstable : (prefixWord ++ tailWord_2996565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996565).length < 2 ^ (prefixWord ++ tailWord_2996565).sum := by decide
  have hdescent : baseEnd_2996565 < baseStart_2996565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996567 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2996567 : Nat := 118140960795 + 2996567 * 2 ^ 59
def prefixEnd_2996567 : Nat := 4983230072969 + 3 ^ 40 * 2996567 * 2
def baseEnd_2996567 : Nat := 1538679184401482651531545

theorem tailTrace_2996567 : CollatzResearch.WordTrace tailWord_2996567 prefixEnd_2996567 1538679184401482651531545 := by
  unfold tailWord_2996567
  simp only [CollatzResearch.WordTrace]
  refine ⟨109293777334957006744387955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72862518223304671162925303 109293777334957006744387955)
  ·
    refine ⟨163940666002435510116581933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109293777334957006744387955 163940666002435510116581933)
    ·
      refine ⟨61477749750913316293718225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163940666002435510116581933 61477749750913316293718225)
      ·
        refine ⟨46108312313184987220288669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61477749750913316293718225 46108312313184987220288669)
        ·
          refine ⟨17290617117444370207608251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46108312313184987220288669 17290617117444370207608251)
          ·
            refine ⟨25935925676166555311412377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17290617117444370207608251 25935925676166555311412377)
            ·
              refine ⟨19451944257124916483559283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25935925676166555311412377 19451944257124916483559283)
              ·
                refine ⟨29177916385687374725338925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19451944257124916483559283 29177916385687374725338925)
                ·
                  refine ⟨10941718644632765522002097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29177916385687374725338925 10941718644632765522002097)
                  ·
                    refine ⟨8206288983474574141501573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10941718644632765522002097 8206288983474574141501573)
                    ·
                      refine ⟨1538679184401482651531545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8206288983474574141501573 1538679184401482651531545)
                      ·
                        rfl

theorem cell23_2996567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2996567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996567 prefixEnd_2996567 := by exact prefixLift 2996567
  have htrace : WordTrace (prefixWord ++ tailWord_2996567) baseStart_2996567 baseEnd_2996567 := by
    simpa [prefixWord, tailWord_2996567, baseEnd_2996567] using wordTrace_append hprefix tailTrace_2996567
  have hstable : (prefixWord ++ tailWord_2996567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996567).length < 2 ^ (prefixWord ++ tailWord_2996567).sum := by decide
  have hdescent : baseEnd_2996567 < baseStart_2996567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996587 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 3]
def baseStart_2996587 : Nat := 118140960795 + 2996587 * 2 ^ 59
def prefixEnd_2996587 : Nat := 4983230072969 + 3 ^ 40 * 2996587 * 2
def baseEnd_2996587 : Nat := 1538689454014572573281453

theorem tailTrace_2996587 : CollatzResearch.WordTrace tailWord_2996587 prefixEnd_2996587 1538689454014572573281453 := by
  unfold tailWord_2996587
  simp only [CollatzResearch.WordTrace]
  refine ⟨109294506794884550160116015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72863004529923033440077343 109294506794884550160116015)
  ·
    refine ⟨163941760192326825240174023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109294506794884550160116015 163941760192326825240174023)
    ·
      refine ⟨245912640288490237860261035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163941760192326825240174023 245912640288490237860261035)
      ·
        refine ⟨368868960432735356790391553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245912640288490237860261035 368868960432735356790391553)
        ·
          refine ⟨276651720324551517592793665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368868960432735356790391553 276651720324551517592793665)
          ·
            refine ⟨207488790243413638194595249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276651720324551517592793665 207488790243413638194595249)
            ·
              refine ⟨155616592682560228645946437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207488790243413638194595249 155616592682560228645946437)
              ·
                refine ⟨29178111127980042871114957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155616592682560228645946437 29178111127980042871114957)
                ·
                  refine ⟨10941791672992516076668109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29178111127980042871114957 10941791672992516076668109)
                  ·
                    refine ⟨4103171877372193528750541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10941791672992516076668109 4103171877372193528750541)
                    ·
                      refine ⟨1538689454014572573281453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103171877372193528750541 1538689454014572573281453)
                      ·
                        rfl

theorem cell23_2996587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 3].length) (baseStart_2996587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996587 prefixEnd_2996587 := by exact prefixLift 2996587
  have htrace : WordTrace (prefixWord ++ tailWord_2996587) baseStart_2996587 baseEnd_2996587 := by
    simpa [prefixWord, tailWord_2996587, baseEnd_2996587] using wordTrace_append hprefix tailTrace_2996587
  have hstable : (prefixWord ++ tailWord_2996587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996587).length < 2 ^ (prefixWord ++ tailWord_2996587).sum := by decide
  have hdescent : baseEnd_2996587 < baseStart_2996587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996604 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_2996604 : Nat := 118140960795 + 2996604 * 2 ^ 59
def prefixEnd_2996604 : Nat := 4983230072969 + 3 ^ 40 * 2996604 * 2
def baseEnd_2996604 : Nat := 1538698183185699006768875

theorem tailTrace_2996604 : CollatzResearch.WordTrace tailWord_2996604 prefixEnd_2996604 1538698183185699006768875 := by
  unfold tailWord_2996604
  simp only [CollatzResearch.WordTrace]
  refine ⟨54647563417911481031742433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72863417890548641375656577 54647563417911481031742433)
  ·
    refine ⟨40985672563433610773806825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54647563417911481031742433 40985672563433610773806825)
    ·
      refine ⟨30739254422575208080355119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40985672563433610773806825 30739254422575208080355119)
      ·
        refine ⟨46108881633862812120532679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30739254422575208080355119 46108881633862812120532679)
        ·
          refine ⟨69163322450794218180799019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46108881633862812120532679 69163322450794218180799019)
          ·
            refine ⟨103744983676191327271198529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69163322450794218180799019 103744983676191327271198529)
            ·
              refine ⟨77808737757143495453398897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103744983676191327271198529 77808737757143495453398897)
              ·
                refine ⟨58356553317857621590049173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77808737757143495453398897 58356553317857621590049173)
                ·
                  refine ⟨2735463436774576012033555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58356553317857621590049173 2735463436774576012033555)
                  ·
                    refine ⟨4103195155161864018050333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735463436774576012033555 4103195155161864018050333)
                    ·
                      refine ⟨1538698183185699006768875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103195155161864018050333 1538698183185699006768875)
                      ·
                        rfl

theorem cell23_2996604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_2996604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996604 prefixEnd_2996604 := by exact prefixLift 2996604
  have htrace : WordTrace (prefixWord ++ tailWord_2996604) baseStart_2996604 baseEnd_2996604 := by
    simpa [prefixWord, tailWord_2996604, baseEnd_2996604] using wordTrace_append hprefix tailTrace_2996604
  have hstable : (prefixWord ++ tailWord_2996604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996604).length < 2 ^ (prefixWord ++ tailWord_2996604).sum := by decide
  have hdescent : baseEnd_2996604 < baseStart_2996604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996631 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 1, 3, 2]
def baseStart_2996631 : Nat := 118140960795 + 2996631 * 2 ^ 59
def prefixEnd_2996631 : Nat := 4983230072969 + 3 ^ 40 * 2996631 * 2
def baseEnd_2996631 : Nat := 1538712047163370401131251

theorem tailTrace_2996631 : CollatzResearch.WordTrace tailWord_2996631 prefixEnd_2996631 1538712047163370401131251 := by
  unfold tailWord_2996631
  simp only [CollatzResearch.WordTrace]
  refine ⟨109296111606725145674717747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72864074404483430449811831 109296111606725145674717747)
  ·
    refine ⟨163944167410087718512076621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109296111606725145674717747 163944167410087718512076621)
    ·
      refine ⟨61479062778782894442028733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163944167410087718512076621 61479062778782894442028733)
      ·
        refine ⟨23054648542043585415760775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61479062778782894442028733 23054648542043585415760775)
        ·
          refine ⟨34581972813065378123641163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23054648542043585415760775 34581972813065378123641163)
          ·
            refine ⟨51872959219598067185461745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34581972813065378123641163 51872959219598067185461745)
            ·
              refine ⟨38904719414698550389096309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51872959219598067185461745 38904719414698550389096309)
              ·
                refine ⟨3647317445127989098977779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38904719414698550389096309 3647317445127989098977779)
                ·
                  refine ⟨5470976167691983648466669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647317445127989098977779 5470976167691983648466669)
                  ·
                    refine ⟨2051616062884493868175001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5470976167691983648466669 2051616062884493868175001)
                    ·
                      refine ⟨1538712047163370401131251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051616062884493868175001 1538712047163370401131251)
                      ·
                        rfl

theorem cell23_2996631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_2996631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996631 prefixEnd_2996631 := by exact prefixLift 2996631
  have htrace : WordTrace (prefixWord ++ tailWord_2996631) baseStart_2996631 baseEnd_2996631 := by
    simpa [prefixWord, tailWord_2996631, baseEnd_2996631] using wordTrace_append hprefix tailTrace_2996631
  have hstable : (prefixWord ++ tailWord_2996631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996631).length < 2 ^ (prefixWord ++ tailWord_2996631).sum := by decide
  have hdescent : baseEnd_2996631 < baseStart_2996631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996648 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2996648 : Nat := 118140960795 + 2996648 * 2 ^ 59
def prefixEnd_2996648 : Nat := 4983230072969 + 3 ^ 40 * 2996648 * 2
def baseEnd_2996648 : Nat := 1538720776334496834618673

theorem tailTrace_2996648 : CollatzResearch.WordTrace tailWord_2996648 prefixEnd_2996648 1538720776334496834618673 := by
  unfold tailWord_2996648
  simp only [CollatzResearch.WordTrace]
  refine ⟨54648365823831778789043299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72864487765109038385391065 54648365823831778789043299)
  ·
    refine ⟨81972548735747668183564949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54648365823831778789043299 81972548735747668183564949)
    ·
      refine ⟨3842463221988171946104607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81972548735747668183564949 3842463221988171946104607)
      ·
        refine ⟨5763694832982257919156911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842463221988171946104607 5763694832982257919156911)
        ·
          refine ⟨8645542249473386878735367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763694832982257919156911 8645542249473386878735367)
          ·
            refine ⟨12968313374210080318103051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645542249473386878735367 12968313374210080318103051)
            ·
              refine ⟨19452470061315120477154577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12968313374210080318103051 19452470061315120477154577)
              ·
                refine ⟨14589352545986340357865933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19452470061315120477154577 14589352545986340357865933)
                ·
                  refine ⟨5471007204744877634199725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14589352545986340357865933 5471007204744877634199725)
                  ·
                    refine ⟨2051627701779329112824897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5471007204744877634199725 2051627701779329112824897)
                    ·
                      refine ⟨1538720776334496834618673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051627701779329112824897 1538720776334496834618673)
                      ·
                        rfl

theorem cell23_2996648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2996648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996648 prefixEnd_2996648 := by exact prefixLift 2996648
  have htrace : WordTrace (prefixWord ++ tailWord_2996648) baseStart_2996648 baseEnd_2996648 := by
    simpa [prefixWord, tailWord_2996648, baseEnd_2996648] using wordTrace_append hprefix tailTrace_2996648
  have hstable : (prefixWord ++ tailWord_2996648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996648).length < 2 ^ (prefixWord ++ tailWord_2996648).sum := by decide
  have hdescent : baseEnd_2996648 < baseStart_2996648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996701 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 5]
def baseStart_2996701 : Nat := 118140960795 + 2996701 * 2 ^ 59
def prefixEnd_2996701 : Nat := 4983230072969 + 3 ^ 40 * 2996701 * 2
def baseEnd_2996701 : Nat := 170971998978798347472881

theorem tailTrace_2996701 : CollatzResearch.WordTrace tailWord_2996701 prefixEnd_2996701 170971998978798347472881 := by
  unfold tailWord_2996701
  simp only [CollatzResearch.WordTrace]
  refine ⟨109298664716471547629765957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72865776477647698419843971 109298664716471547629765957)
  ·
    refine ⟨20493499634338415180581117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109298664716471547629765957 20493499634338415180581117)
    ·
      refine ⟨7685062362876905692717919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20493499634338415180581117 7685062362876905692717919)
      ·
        refine ⟨11527593544315358539076879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685062362876905692717919 11527593544315358539076879)
        ·
          refine ⟨17291390316473037808615319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11527593544315358539076879 17291390316473037808615319)
          ·
            refine ⟨25937085474709556712922979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17291390316473037808615319 25937085474709556712922979)
            ·
              refine ⟨38905628212064335069384469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25937085474709556712922979 38905628212064335069384469)
              ·
                refine ⟨1823701322440515706377397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38905628212064335069384469 1823701322440515706377397)
                ·
                  refine ⟨170971998978798347472881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823701322440515706377397 170971998978798347472881)
                  ·
                    rfl

theorem cell23_2996701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_2996701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996701 prefixEnd_2996701 := by exact prefixLift 2996701
  have htrace : WordTrace (prefixWord ++ tailWord_2996701) baseStart_2996701 baseEnd_2996701 := by
    simpa [prefixWord, tailWord_2996701, baseEnd_2996701] using wordTrace_append hprefix tailTrace_2996701
  have hstable : (prefixWord ++ tailWord_2996701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996701).length < 2 ^ (prefixWord ++ tailWord_2996701).sum := by decide
  have hdescent : baseEnd_2996701 < baseStart_2996701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996714 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_2996714 : Nat := 118140960795 + 2996714 * 2 ^ 59
def prefixEnd_2996714 : Nat := 4983230072969 + 3 ^ 40 * 2996714 * 2
def baseEnd_2996714 : Nat := 512918222019231192131123

theorem tailTrace_2996714 : CollatzResearch.WordTrace tailWord_2996714 prefixEnd_2996714 512918222019231192131123 := by
  unfold tailWord_2996714
  simp only [CollatzResearch.WordTrace]
  refine ⟨27324784716356112712497299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72866092576949633899992797 27324784716356112712497299)
  ·
    refine ⟨40987177074534169068745949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27324784716356112712497299 40987177074534169068745949)
    ·
      refine ⟨15370191402950313400779731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40987177074534169068745949 15370191402950313400779731)
      ·
        refine ⟨23055287104425470101169597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370191402950313400779731 23055287104425470101169597)
        ·
          refine ⟨8645732664159551287938599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23055287104425470101169597 8645732664159551287938599)
          ·
            refine ⟨12968598996239326931907899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645732664159551287938599 12968598996239326931907899)
            ·
              refine ⟨19452898494358990397861849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12968598996239326931907899 19452898494358990397861849)
              ·
                refine ⟨14589673870769242798396387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19452898494358990397861849 14589673870769242798396387)
                ·
                  refine ⟨21884510806153864197594581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14589673870769242798396387 21884510806153864197594581)
                  ·
                    refine ⟨512918222019231192131123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21884510806153864197594581 512918222019231192131123)
                    ·
                      rfl

theorem cell23_2996714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_2996714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996714 prefixEnd_2996714 := by exact prefixLift 2996714
  have htrace : WordTrace (prefixWord ++ tailWord_2996714) baseStart_2996714 baseEnd_2996714 := by
    simpa [prefixWord, tailWord_2996714, baseEnd_2996714] using wordTrace_append hprefix tailTrace_2996714
  have hstable : (prefixWord ++ tailWord_2996714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996714).length < 2 ^ (prefixWord ++ tailWord_2996714).sum := by decide
  have hdescent : baseEnd_2996714 < baseStart_2996714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996784 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_2996784 : Nat := 118140960795 + 2996784 * 2 ^ 59
def prefixEnd_2996784 : Nat := 4983230072969 + 3 ^ 40 * 2996784 * 2
def baseEnd_2996784 : Nat := 1538790609703508302518047

theorem tailTrace_2996784 : CollatzResearch.WordTrace tailWord_2996784 prefixEnd_2996784 1538790609703508302518047 := by
  unfold tailWord_2996784
  simp only [CollatzResearch.WordTrace]
  refine ⟨54650845987585426402518703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72867794650113901870024937 54650845987585426402518703)
  ·
    refine ⟨81976268981378139603778055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54650845987585426402518703 81976268981378139603778055)
    ·
      refine ⟨122964403472067209405667083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81976268981378139603778055 122964403472067209405667083)
      ·
        refine ⟨184446605208100814108500625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122964403472067209405667083 184446605208100814108500625)
        ·
          refine ⟨138334953906075610581375469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184446605208100814108500625 138334953906075610581375469)
          ·
            refine ⟨51875607714778353968015801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138334953906075610581375469 51875607714778353968015801)
            ·
              refine ⟨38906705786083765476011851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51875607714778353968015801 38906705786083765476011851)
              ·
                refine ⟨58360058679125648214017777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38906705786083765476011851 58360058679125648214017777)
                ·
                  refine ⟨43770044009344236160513333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58360058679125648214017777 43770044009344236160513333)
                  ·
                    refine ⟨4103441625876022140048125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43770044009344236160513333 4103441625876022140048125)
                    ·
                      refine ⟨1538790609703508302518047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103441625876022140048125 1538790609703508302518047)
                      ·
                        rfl

theorem cell23_2996784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_2996784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996784 prefixEnd_2996784 := by exact prefixLift 2996784
  have htrace : WordTrace (prefixWord ++ tailWord_2996784) baseStart_2996784 baseEnd_2996784 := by
    simpa [prefixWord, tailWord_2996784, baseEnd_2996784] using wordTrace_append hprefix tailTrace_2996784
  have hstable : (prefixWord ++ tailWord_2996784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996784).length < 2 ^ (prefixWord ++ tailWord_2996784).sum := by decide
  have hdescent : baseEnd_2996784 < baseStart_2996784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996818 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2996818 : Nat := 118140960795 + 2996818 * 2 ^ 59
def prefixEnd_2996818 : Nat := 4983230072969 + 3 ^ 40 * 2996818 * 2
def baseEnd_2996818 : Nat := 1538808068045761169492891

theorem tailTrace_2996818 : CollatzResearch.WordTrace tailWord_2996818 prefixEnd_2996818 1538808068045761169492891 := by
  unfold tailWord_2996818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27325733014261919152943777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72868621371365117741183405 27325733014261919152943777)
  ·
    refine ⟨20494299760696439364707833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27325733014261919152943777 20494299760696439364707833)
    ·
      refine ⟨15370724820522329523530875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20494299760696439364707833 15370724820522329523530875)
      ·
        refine ⟨23056087230783494285296313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370724820522329523530875 23056087230783494285296313)
        ·
          refine ⟨17292065423087620713972235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23056087230783494285296313 17292065423087620713972235)
          ·
            refine ⟨25938098134631431070958353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17292065423087620713972235 25938098134631431070958353)
            ·
              refine ⟨19453573600973573303218765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25938098134631431070958353 19453573600973573303218765)
              ·
                refine ⟨7295090100365089988707037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19453573600973573303218765 7295090100365089988707037)
                ·
                  refine ⟨2735658787636908745765139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7295090100365089988707037 2735658787636908745765139)
                  ·
                    refine ⟨4103488181455363118647709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735658787636908745765139 4103488181455363118647709)
                    ·
                      refine ⟨1538808068045761169492891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103488181455363118647709 1538808068045761169492891)
                      ·
                        rfl

theorem cell23_2996818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2996818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996818 prefixEnd_2996818 := by exact prefixLift 2996818
  have htrace : WordTrace (prefixWord ++ tailWord_2996818) baseStart_2996818 baseEnd_2996818 := by
    simpa [prefixWord, tailWord_2996818, baseEnd_2996818] using wordTrace_append hprefix tailTrace_2996818
  have hstable : (prefixWord ++ tailWord_2996818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996818).length < 2 ^ (prefixWord ++ tailWord_2996818).sum := by decide
  have hdescent : baseEnd_2996818 < baseStart_2996818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996841 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 4]
def baseStart_2996841 : Nat := 118140960795 + 2996841 * 2 ^ 59
def prefixEnd_2996841 : Nat := 4983230072969 + 3 ^ 40 * 2996841 * 2
def baseEnd_2996841 : Nat := 1538819878100814579505285

theorem tailTrace_2996841 : CollatzResearch.WordTrace tailWord_2996841 prefixEnd_2996841 1538819878100814579505285 := by
  unfold tailWord_2996841
  simp only [CollatzResearch.WordTrace]
  refine ⟨109303770935964351539862377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72869180623976234359908251 109303770935964351539862377)
  ·
    refine ⟨81977828201973263654896783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109303770935964351539862377 81977828201973263654896783)
    ·
      refine ⟨122966742302959895482345175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81977828201973263654896783 122966742302959895482345175)
      ·
        refine ⟨184450113454439843223517763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122966742302959895482345175 184450113454439843223517763)
        ·
          refine ⟨276675170181659764835276645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184450113454439843223517763 276675170181659764835276645)
          ·
            refine ⟨51876594409061205906614371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276675170181659764835276645 51876594409061205906614371)
            ·
              refine ⟨77814891613591808859921557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51876594409061205906614371 77814891613591808859921557)
              ·
                refine ⟨3647573044387116040308823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77814891613591808859921557 3647573044387116040308823)
                ·
                  refine ⟨5471359566580674060463235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647573044387116040308823 5471359566580674060463235)
                  ·
                    refine ⟨8207039349871011090694853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471359566580674060463235 8207039349871011090694853)
                    ·
                      refine ⟨1538819878100814579505285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8207039349871011090694853 1538819878100814579505285)
                      ·
                        rfl

theorem cell23_2996841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_2996841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996841 prefixEnd_2996841 := by exact prefixLift 2996841
  have htrace : WordTrace (prefixWord ++ tailWord_2996841) baseStart_2996841 baseEnd_2996841 := by
    simpa [prefixWord, tailWord_2996841, baseEnd_2996841] using wordTrace_append hprefix tailTrace_2996841
  have hstable : (prefixWord ++ tailWord_2996841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996841).length < 2 ^ (prefixWord ++ tailWord_2996841).sum := by decide
  have hdescent : baseEnd_2996841 < baseStart_2996841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996845 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_2996845 : Nat := 118140960795 + 2996845 * 2 ^ 59
def prefixEnd_2996845 : Nat := 4983230072969 + 3 ^ 40 * 2996845 * 2
def baseEnd_2996845 : Nat := 1538821932023432563855267

theorem tailTrace_2996845 : CollatzResearch.WordTrace tailWord_2996845 prefixEnd_2996845 1538821932023432563855267 := by
  unfold tailWord_2996845
  simp only [CollatzResearch.WordTrace]
  refine ⟨109303916827949860223007989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72869277885299906815338659 109303916827949860223007989)
  ·
    refine ⟨10247242202620299395906999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109303916827949860223007989 10247242202620299395906999)
    ·
      refine ⟨15370863303930449093860499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247242202620299395906999 15370863303930449093860499)
      ·
        refine ⟨23056294955895673640790749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370863303930449093860499 23056294955895673640790749)
        ·
          refine ⟨8646110608460877615296531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23056294955895673640790749 8646110608460877615296531)
          ·
            refine ⟨12969165912691316422944797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646110608460877615296531 12969165912691316422944797)
            ·
              refine ⟨4863437217259243658604299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12969165912691316422944797 4863437217259243658604299)
              ·
                refine ⟨7295155825888865487906449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863437217259243658604299 7295155825888865487906449)
                ·
                  refine ⟨5471366869416649115929837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295155825888865487906449 5471366869416649115929837)
                  ·
                    refine ⟨2051762576031243418473689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5471366869416649115929837 2051762576031243418473689)
                    ·
                      refine ⟨1538821932023432563855267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051762576031243418473689 1538821932023432563855267)
                      ·
                        rfl

theorem cell23_2996845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_2996845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996845 prefixEnd_2996845 := by exact prefixLift 2996845
  have htrace : WordTrace (prefixWord ++ tailWord_2996845) baseStart_2996845 baseEnd_2996845 := by
    simpa [prefixWord, tailWord_2996845, baseEnd_2996845] using wordTrace_append hprefix tailTrace_2996845
  have hstable : (prefixWord ++ tailWord_2996845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996845).length < 2 ^ (prefixWord ++ tailWord_2996845).sum := by decide
  have hdescent : baseEnd_2996845 < baseStart_2996845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996864 : List Nat := [2, 1, 1, 2, 1, 6, 10]
def baseStart_2996864 : Nat := 118140960795 + 2996864 * 2 ^ 59
def prefixEnd_2996864 : Nat := 4983230072969 + 3 ^ 40 * 2996864 * 2
def baseEnd_2996864 : Nat := 18997922075998370240959

theorem tailTrace_2996864 : CollatzResearch.WordTrace tailWord_2996864 prefixEnd_2996864 18997922075998370240959 := by
  unfold tailWord_2996864
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652304907440513233974823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72869739876587350978633097 54652304907440513233974823)
  ·
    refine ⟨81978457361160769850962235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54652304907440513233974823 81978457361160769850962235)
    ·
      refine ⟨122967686041741154776443353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81978457361160769850962235 122967686041741154776443353)
      ·
        refine ⟨92225764531305866082332515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122967686041741154776443353 92225764531305866082332515)
        ·
          refine ⟨138338646796958799123498773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92225764531305866082332515 138338646796958799123498773)
          ·
            refine ⟨6484624068607443708914005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138338646796958799123498773 6484624068607443708914005)
            ·
              refine ⟨18997922075998370240959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6484624068607443708914005 18997922075998370240959)
              ·
                rfl

theorem cell23_2996864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 10].length) (baseStart_2996864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996864 prefixEnd_2996864 := by exact prefixLift 2996864
  have htrace : WordTrace (prefixWord ++ tailWord_2996864) baseStart_2996864 baseEnd_2996864 := by
    simpa [prefixWord, tailWord_2996864, baseEnd_2996864] using wordTrace_append hprefix tailTrace_2996864
  have hstable : (prefixWord ++ tailWord_2996864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996864).length < 2 ^ (prefixWord ++ tailWord_2996864).sum := by decide
  have hdescent : baseEnd_2996864 < baseStart_2996864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996868 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_2996868 : Nat := 118140960795 + 2996868 * 2 ^ 59
def prefixEnd_2996868 : Nat := 4983230072969 + 3 ^ 40 * 2996868 * 2
def baseEnd_2996868 : Nat := 512944580692828657955887

theorem tailTrace_2996868 : CollatzResearch.WordTrace tailWord_2996868 prefixEnd_2996868 512944580692828657955887 := by
  unfold tailWord_2996868
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652377853433267575547629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72869837137911023434063505 54652377853433267575547629)
  ·
    refine ⟨20494641695037475340830361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54652377853433267575547629 20494641695037475340830361)
    ·
      refine ⟨15370981271278106505622771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20494641695037475340830361 15370981271278106505622771)
      ·
        refine ⟨23056471906917159758434157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370981271278106505622771 23056471906917159758434157)
        ·
          refine ⟨8646176965093934909412809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23056471906917159758434157 8646176965093934909412809)
          ·
            refine ⟨6484632723820451182059607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8646176965093934909412809 6484632723820451182059607)
            ·
              refine ⟨9726949085730676773089411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484632723820451182059607 9726949085730676773089411)
              ·
                refine ⟨14590423628596015159634117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9726949085730676773089411 14590423628596015159634117)
                ·
                  refine ⟨2735704430361752842431397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14590423628596015159634117 2735704430361752842431397)
                  ·
                    refine ⟨512944580692828657955887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2735704430361752842431397 512944580692828657955887)
                    ·
                      rfl

theorem cell23_2996868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_2996868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996868 prefixEnd_2996868 := by exact prefixLift 2996868
  have htrace : WordTrace (prefixWord ++ tailWord_2996868) baseStart_2996868 baseEnd_2996868 := by
    simpa [prefixWord, tailWord_2996868, baseEnd_2996868] using wordTrace_append hprefix tailTrace_2996868
  have hstable : (prefixWord ++ tailWord_2996868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996868).length < 2 ^ (prefixWord ++ tailWord_2996868).sum := by decide
  have hdescent : baseEnd_2996868 < baseStart_2996868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996909 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_2996909 : Nat := 118140960795 + 2996909 * 2 ^ 59
def prefixEnd_2996909 : Nat := 4983230072969 + 3 ^ 40 * 2996909 * 2
def baseEnd_2996909 : Nat := 1538854794785320313454973

theorem tailTrace_2996909 : CollatzResearch.WordTrace tailWord_2996909 prefixEnd_2996909 1538854794785320313454973 := by
  unfold tailWord_2996909
  simp only [CollatzResearch.WordTrace]
  refine ⟨109306251099717999153337781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72870834066478666102225187 109306251099717999153337781)
  ·
    refine ⟨10247461040598562420625417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109306251099717999153337781 10247461040598562420625417)
    ·
      refine ⟨7685595780448921815469063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10247461040598562420625417 7685595780448921815469063)
      ·
        refine ⟨11528393670673382723203595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685595780448921815469063 11528393670673382723203595)
        ·
          refine ⟨17292590506010074084805393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528393670673382723203595 17292590506010074084805393)
          ·
            refine ⟨12969442879507555563604045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17292590506010074084805393 12969442879507555563604045)
            ·
              refine ⟨4863541079815333336351517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12969442879507555563604045 4863541079815333336351517)
              ·
                refine ⟨1823827904930750001131819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4863541079815333336351517 1823827904930750001131819)
                ·
                  refine ⟨2735741857396125001697729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823827904930750001131819 2735741857396125001697729)
                  ·
                    refine ⟨2051806393047093751273297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2735741857396125001697729 2051806393047093751273297)
                    ·
                      refine ⟨1538854794785320313454973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051806393047093751273297 1538854794785320313454973)
                      ·
                        rfl

theorem cell23_2996909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_2996909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996909 prefixEnd_2996909 := by exact prefixLift 2996909
  have htrace : WordTrace (prefixWord ++ tailWord_2996909) baseStart_2996909 baseEnd_2996909 := by
    simpa [prefixWord, tailWord_2996909, baseEnd_2996909] using wordTrace_append hprefix tailTrace_2996909
  have hstable : (prefixWord ++ tailWord_2996909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996909).length < 2 ^ (prefixWord ++ tailWord_2996909).sum := by decide
  have hdescent : baseEnd_2996909 < baseStart_2996909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996942 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_2996942 : Nat := 118140960795 + 2996942 * 2 ^ 59
def prefixEnd_2996942 : Nat := 4983230072969 + 3 ^ 40 * 2996942 * 2
def baseEnd_2996942 : Nat := 1538871739646918684342321

theorem tailTrace_2996942 : CollatzResearch.WordTrace tailWord_2996942 prefixEnd_2996942 1538871739646918684342321 := by
  unfold tailWord_2996942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663431838574805723661135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72871636472398963859526053 13663431838574805723661135)
  ·
    refine ⟨20495147757862208585491703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13663431838574805723661135 20495147757862208585491703)
    ·
      refine ⟨30742721636793312878237555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20495147757862208585491703 30742721636793312878237555)
      ·
        refine ⟨46114082455189969317356333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30742721636793312878237555 46114082455189969317356333)
        ·
          refine ⟨17292780920696238494008625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46114082455189969317356333 17292780920696238494008625)
          ·
            refine ⟨12969585690522178870506469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17292780920696238494008625 12969585690522178870506469)
            ·
              refine ⟨2431797316972908538219963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12969585690522178870506469 2431797316972908538219963)
              ·
                refine ⟨3647695975459362807329945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431797316972908538219963 3647695975459362807329945)
                ·
                  refine ⟨2735771981594522105497459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3647695975459362807329945 2735771981594522105497459)
                  ·
                    refine ⟨4103657972391783158246189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735771981594522105497459 4103657972391783158246189)
                    ·
                      refine ⟨1538871739646918684342321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103657972391783158246189 1538871739646918684342321)
                      ·
                        rfl

theorem cell23_2996942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_2996942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996942 prefixEnd_2996942 := by exact prefixLift 2996942
  have htrace : WordTrace (prefixWord ++ tailWord_2996942) baseStart_2996942 baseEnd_2996942 := by
    simpa [prefixWord, tailWord_2996942, baseEnd_2996942] using wordTrace_append hprefix tailTrace_2996942
  have hstable : (prefixWord ++ tailWord_2996942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996942).length < 2 ^ (prefixWord ++ tailWord_2996942).sum := by decide
  have hdescent : baseEnd_2996942 < baseStart_2996942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996951 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2996951 : Nat := 118140960795 + 2996951 * 2 ^ 59
def prefixEnd_2996951 : Nat := 4983230072969 + 3 ^ 40 * 2996951 * 2
def baseEnd_2996951 : Nat := 1538876360972809149129779

theorem tailTrace_2996951 : CollatzResearch.WordTrace tailWord_2996951 prefixEnd_2996951 1538876360972809149129779 := by
  unfold tailWord_2996951
  simp only [CollatzResearch.WordTrace]
  refine ⟨109307782965565840326366707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72871855310377226884244471 109307782965565840326366707)
  ·
    refine ⟨163961674448348760489550061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109307782965565840326366707 163961674448348760489550061)
    ·
      refine ⟨61485627918130785183581273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163961674448348760489550061 61485627918130785183581273)
      ·
        refine ⟨46114220938598088887685955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61485627918130785183581273 46114220938598088887685955)
        ·
          refine ⟨69171331407897133331528933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46114220938598088887685955 69171331407897133331528933)
          ·
            refine ⟨12969624638980712499661675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69171331407897133331528933 12969624638980712499661675)
            ·
              refine ⟨19454436958471068749492513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12969624638980712499661675 19454436958471068749492513)
              ·
                refine ⟨14590827718853301562119385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19454436958471068749492513 14590827718853301562119385)
                ·
                  refine ⟨10943120789139976171589539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14590827718853301562119385 10943120789139976171589539)
                  ·
                    refine ⟨16414681183709964257384309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10943120789139976171589539 16414681183709964257384309)
                    ·
                      refine ⟨1538876360972809149129779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16414681183709964257384309 1538876360972809149129779)
                      ·
                        rfl

theorem cell23_2996951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2996951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996951 prefixEnd_2996951 := by exact prefixLift 2996951
  have htrace : WordTrace (prefixWord ++ tailWord_2996951) baseStart_2996951 baseEnd_2996951 := by
    simpa [prefixWord, tailWord_2996951, baseEnd_2996951] using wordTrace_append hprefix tailTrace_2996951
  have hstable : (prefixWord ++ tailWord_2996951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996951).length < 2 ^ (prefixWord ++ tailWord_2996951).sum := by decide
  have hdescent : baseEnd_2996951 < baseStart_2996951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996952 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 1, 3, 2]
def baseStart_2996952 : Nat := 118140960795 + 2996952 * 2 ^ 59
def prefixEnd_2996952 : Nat := 4983230072969 + 3 ^ 40 * 2996952 * 2
def baseEnd_2996952 : Nat := 1538876874453463645217275

theorem tailTrace_2996952 : CollatzResearch.WordTrace tailWord_2996952 prefixEnd_2996952 1538876874453463645217275 := by
  unfold tailWord_2996952
  simp only [CollatzResearch.WordTrace]
  refine ⟨54653909719281108748576555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72871879625708144998102073 54653909719281108748576555)
  ·
    refine ⟨81980864578921663122864833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54653909719281108748576555 81980864578921663122864833)
    ·
      refine ⟨61485648434191247342148625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81980864578921663122864833 61485648434191247342148625)
      ·
        refine ⟨46114236325643435506611469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61485648434191247342148625 46114236325643435506611469)
        ·
          refine ⟨17292838622116288314979301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46114236325643435506611469 17292838622116288314979301)
          ·
            refine ⟨3242407241646804059058619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17292838622116288314979301 3242407241646804059058619)
            ·
              refine ⟨4863610862470206088587929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242407241646804059058619 4863610862470206088587929)
              ·
                refine ⟨3647708146852654566440947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863610862470206088587929 3647708146852654566440947)
                ·
                  refine ⟨5471562220278981849661421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647708146852654566440947 5471562220278981849661421)
                  ·
                    refine ⟨2051835832604618193623033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5471562220278981849661421 2051835832604618193623033)
                    ·
                      refine ⟨1538876874453463645217275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051835832604618193623033 1538876874453463645217275)
                      ·
                        rfl

theorem cell23_2996952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_2996952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996952 prefixEnd_2996952 := by exact prefixLift 2996952
  have htrace : WordTrace (prefixWord ++ tailWord_2996952) baseStart_2996952 baseEnd_2996952 := by
    simpa [prefixWord, tailWord_2996952, baseEnd_2996952] using wordTrace_append hprefix tailTrace_2996952
  have hstable : (prefixWord ++ tailWord_2996952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996952).length < 2 ^ (prefixWord ++ tailWord_2996952).sum := by decide
  have hdescent : baseEnd_2996952 < baseStart_2996952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996965 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2996965 : Nat := 118140960795 + 2996965 * 2 ^ 59
def prefixEnd_2996965 : Nat := 4983230072969 + 3 ^ 40 * 2996965 * 2
def baseEnd_2996965 : Nat := 1538883549701972094354715

theorem tailTrace_2996965 : CollatzResearch.WordTrace tailWord_2996965 prefixEnd_2996965 1538883549701972094354715 := by
  unfold tailWord_2996965
  simp only [CollatzResearch.WordTrace]
  refine ⟨109308293587515120717376349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72872195725010080478250899 109308293587515120717376349)
  ·
    refine ⟨40990610095318170269016131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109308293587515120717376349 40990610095318170269016131)
    ·
      refine ⟨61485915142977255403524197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40990610095318170269016131 61485915142977255403524197)
      ·
        refine ⟨11528609089308235388160787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61485915142977255403524197 11528609089308235388160787)
        ·
          refine ⟨17292913633962353082241181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528609089308235388160787 17292913633962353082241181)
          ·
            refine ⟨6484842612735882405840443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17292913633962353082241181 6484842612735882405840443)
            ·
              refine ⟨9727263919103823608760665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484842612735882405840443 9727263919103823608760665)
              ·
                refine ⟨7295447939327867706570499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727263919103823608760665 7295447939327867706570499)
                ·
                  refine ⟨10943171908991801559855749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295447939327867706570499 10943171908991801559855749)
                  ·
                    refine ⟨2051844732935962792472953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10943171908991801559855749 2051844732935962792472953)
                    ·
                      refine ⟨1538883549701972094354715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051844732935962792472953 1538883549701972094354715)
                      ·
                        rfl

theorem cell23_2996965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2996965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2996965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2996965 prefixEnd_2996965 := by exact prefixLift 2996965
  have htrace : WordTrace (prefixWord ++ tailWord_2996965) baseStart_2996965 baseEnd_2996965 := by
    simpa [prefixWord, tailWord_2996965, baseEnd_2996965] using wordTrace_append hprefix tailTrace_2996965
  have hstable : (prefixWord ++ tailWord_2996965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996965).length < 2 ^ (prefixWord ++ tailWord_2996965).sum := by decide
  have hdescent : baseEnd_2996965 < baseStart_2996965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997001 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_2997001 : Nat := 118140960795 + 2997001 * 2 ^ 59
def prefixEnd_2997001 : Nat := 4983230072969 + 3 ^ 40 * 2997001 * 2
def baseEnd_2997001 : Nat := 512967345001844651168183

theorem tailTrace_2997001 : CollatzResearch.WordTrace tailWord_2997001 prefixEnd_2997001 512967345001844651168183 := by
  unfold tailWord_2997001
  simp only [CollatzResearch.WordTrace]
  refine ⟨109309606615384698865686857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72873071076923132577124571 109309606615384698865686857)
  ·
    refine ⟨81982204961538524149265143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109309606615384698865686857 81982204961538524149265143)
    ·
      refine ⟨122973307442307786223897715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81982204961538524149265143 122973307442307786223897715)
      ·
        refine ⟨184459961163461679335846573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122973307442307786223897715 184459961163461679335846573)
        ·
          refine ⟨69172485436298129750942465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184459961163461679335846573 69172485436298129750942465)
          ·
            refine ⟨51879364077223597313206849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69172485436298129750942465 51879364077223597313206849)
            ·
              refine ⟨38909523057917697984905137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51879364077223597313206849 38909523057917697984905137)
              ·
                refine ⟨29182142293438273488678853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38909523057917697984905137 29182142293438273488678853)
                ·
                  refine ⟨5471651680019676279127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29182142293438273488678853 5471651680019676279127285)
                  ·
                    refine ⟨512967345001844651168183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5471651680019676279127285 512967345001844651168183)
                    ·
                      rfl

theorem cell23_2997001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_2997001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997001 prefixEnd_2997001 := by exact prefixLift 2997001
  have htrace : WordTrace (prefixWord ++ tailWord_2997001) baseStart_2997001 baseEnd_2997001 := by
    simpa [prefixWord, tailWord_2997001, baseEnd_2997001] using wordTrace_append hprefix tailTrace_2997001
  have hstable : (prefixWord ++ tailWord_2997001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997001).length < 2 ^ (prefixWord ++ tailWord_2997001).sum := by decide
  have hdescent : baseEnd_2997001 < baseStart_2997001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997055 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 2, 4, 2]
def baseStart_2997055 : Nat := 118140960795 + 2997055 * 2 ^ 59
def prefixEnd_2997055 : Nat := 4983230072969 + 3 ^ 40 * 2997055 * 2
def baseEnd_2997055 : Nat := 1538929762960876742229301

theorem tailTrace_2997055 : CollatzResearch.WordTrace tailWord_2997055 prefixEnd_2997055 1538929762960876742229301 := by
  unfold tailWord_2997055
  simp only [CollatzResearch.WordTrace]
  refine ⟨109311576157189066088152619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72874384104792710725435079 109311576157189066088152619)
  ·
    refine ⟨163967364235783599132228929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109311576157189066088152619 163967364235783599132228929)
    ·
      refine ⟨122975523176837699349171697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163967364235783599132228929 122975523176837699349171697)
      ·
        refine ⟨92231642382628274511878773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122975523176837699349171697 92231642382628274511878773)
        ·
          refine ⟨8646716473371400735488635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92231642382628274511878773 8646716473371400735488635)
          ·
            refine ⟨12970074710057101103232953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646716473371400735488635 12970074710057101103232953)
            ·
              refine ⟨9727556032542825827424715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12970074710057101103232953 9727556032542825827424715)
              ·
                refine ⟨14591334048814238741137073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727556032542825827424715 14591334048814238741137073)
                ·
                  refine ⟨10943500536610679055852805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14591334048814238741137073 10943500536610679055852805)
                  ·
                    refine ⟨2051906350614502322972401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10943500536610679055852805 2051906350614502322972401)
                    ·
                      refine ⟨1538929762960876742229301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2051906350614502322972401 1538929762960876742229301)
                      ·
                        rfl

theorem cell23_2997055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_2997055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997055 prefixEnd_2997055 := by exact prefixLift 2997055
  have htrace : WordTrace (prefixWord ++ tailWord_2997055) baseStart_2997055 baseEnd_2997055 := by
    simpa [prefixWord, tailWord_2997055, baseEnd_2997055] using wordTrace_append hprefix tailTrace_2997055
  have hstable : (prefixWord ++ tailWord_2997055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997055).length < 2 ^ (prefixWord ++ tailWord_2997055).sum := by decide
  have hdescent : baseEnd_2997055 < baseStart_2997055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997082 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_2997082 : Nat := 118140960795 + 2997082 * 2 ^ 59
def prefixEnd_2997082 : Nat := 4983230072969 + 3 ^ 40 * 2997082 * 2
def baseEnd_2997082 : Nat := 512981208979516045530559

theorem tailTrace_2997082 : CollatzResearch.WordTrace tailWord_2997082 prefixEnd_2997082 512981208979516045530559 := by
  unfold tailWord_2997082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328140232022812424846375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72875040618727499799590333 27328140232022812424846375)
  ·
    refine ⟨40992210348034218637269563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27328140232022812424846375 40992210348034218637269563)
    ·
      refine ⟨61488315522051327955904345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40992210348034218637269563 61488315522051327955904345)
      ·
        refine ⟨46116236641538495966928259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61488315522051327955904345 46116236641538495966928259)
        ·
          refine ⟨69174354962307743950392389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46116236641538495966928259 69174354962307743950392389)
          ·
            refine ⟨12970191555432701990698573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69174354962307743950392389 12970191555432701990698573)
            ·
              refine ⟨4863821833287263246511965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12970191555432701990698573 4863821833287263246511965)
              ·
                refine ⟨1823933187482723717441987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4863821833287263246511965 1823933187482723717441987)
                ·
                  refine ⟨2735899781224085576162981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823933187482723717441987 2735899781224085576162981)
                  ·
                    refine ⟨512981208979516045530559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2735899781224085576162981 512981208979516045530559)
                    ·
                      rfl

theorem cell23_2997082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_2997082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997082 prefixEnd_2997082 := by exact prefixLift 2997082
  have htrace : WordTrace (prefixWord ++ tailWord_2997082) baseStart_2997082 baseEnd_2997082 := by
    simpa [prefixWord, tailWord_2997082, baseEnd_2997082] using wordTrace_append hprefix tailTrace_2997082
  have hstable : (prefixWord ++ tailWord_2997082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997082).length < 2 ^ (prefixWord ++ tailWord_2997082).sum := by decide
  have hdescent : baseEnd_2997082 < baseStart_2997082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997125 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_2997125 : Nat := 118140960795 + 2997125 * 2 ^ 59
def prefixEnd_2997125 : Nat := 4983230072969 + 3 ^ 40 * 2997125 * 2
def baseEnd_2997125 : Nat := 512988568868897156117993

theorem tailTrace_2997125 : CollatzResearch.WordTrace tailWord_2997125 prefixEnd_2997125 512988568868897156117993 := by
  unfold tailWord_2997125
  simp only [CollatzResearch.WordTrace]
  refine ⟨109314129266935468043200829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72876086177956978695467219 109314129266935468043200829)
  ·
    refine ⟨40992798475100800516200311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109314129266935468043200829 40992798475100800516200311)
    ·
      refine ⟨61489197712651200774300467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40992798475100800516200311 61489197712651200774300467)
      ·
        refine ⟨92233796568976801161450701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61489197712651200774300467 92233796568976801161450701)
        ·
          refine ⟨34587673713366300435544013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92233796568976801161450701 34587673713366300435544013)
          ·
            refine ⟨12970377642512362663329005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34587673713366300435544013 12970377642512362663329005)
            ·
              refine ⟨4863891615942135998748377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12970377642512362663329005 4863891615942135998748377)
              ·
                refine ⟨3647918711956601999061283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863891615942135998748377 3647918711956601999061283)
                ·
                  refine ⟨5471878067934902998591925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647918711956601999061283 5471878067934902998591925)
                  ·
                    refine ⟨512988568868897156117993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5471878067934902998591925 512988568868897156117993)
                    ·
                      rfl

theorem cell23_2997125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_2997125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997125 prefixEnd_2997125 := by exact prefixLift 2997125
  have htrace : WordTrace (prefixWord ++ tailWord_2997125) baseStart_2997125 baseEnd_2997125 := by
    simpa [prefixWord, tailWord_2997125, baseEnd_2997125] using wordTrace_append hprefix tailTrace_2997125
  have hstable : (prefixWord ++ tailWord_2997125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997125).length < 2 ^ (prefixWord ++ tailWord_2997125).sum := by decide
  have hdescent : baseEnd_2997125 < baseStart_2997125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997155 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 2, 4]
def baseStart_2997155 : Nat := 118140960795 + 2997155 * 2 ^ 59
def prefixEnd_2997155 : Nat := 4983230072969 + 3 ^ 40 * 2997155 * 2
def baseEnd_2997155 : Nat := 512993703675442116992947

theorem tailTrace_2997155 : CollatzResearch.WordTrace tailWord_2997155 prefixEnd_2997155 512993703675442116992947 := by
  unfold tailWord_2997155
  simp only [CollatzResearch.WordTrace]
  refine ⟨109315223456826783166792919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72876815637884522111195279 109315223456826783166792919)
  ·
    refine ⟨163972835185240174750189379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109315223456826783166792919 163972835185240174750189379)
    ·
      refine ⟨245959252777860262125284069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163972835185240174750189379 245959252777860262125284069)
      ·
        refine ⟨46117359895848799148490763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245959252777860262125284069 46117359895848799148490763)
        ·
          refine ⟨69176039843773198722736145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46117359895848799148490763 69176039843773198722736145)
          ·
            refine ⟨51882029882829899042052109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69176039843773198722736145 51882029882829899042052109)
            ·
              refine ⟨19455761206061212140769541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51882029882829899042052109 19455761206061212140769541)
              ·
                refine ⟨3647955226136477276394289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19455761206061212140769541 3647955226136477276394289)
                ·
                  refine ⟨2735966419602357957295717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3647955226136477276394289 2735966419602357957295717)
                  ·
                    refine ⟨512993703675442116992947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2735966419602357957295717 512993703675442116992947)
                    ·
                      rfl

theorem cell23_2997155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 4].length) (baseStart_2997155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997155 prefixEnd_2997155 := by exact prefixLift 2997155
  have htrace : WordTrace (prefixWord ++ tailWord_2997155) baseStart_2997155 baseEnd_2997155 := by
    simpa [prefixWord, tailWord_2997155, baseEnd_2997155] using wordTrace_append hprefix tailTrace_2997155
  have hstable : (prefixWord ++ tailWord_2997155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997155).length < 2 ^ (prefixWord ++ tailWord_2997155).sum := by decide
  have hdescent : baseEnd_2997155 < baseStart_2997155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997172 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2997172 : Nat := 118140960795 + 2997172 * 2 ^ 59
def prefixEnd_2997172 : Nat := 4983230072969 + 3 ^ 40 * 2997172 * 2
def baseEnd_2997172 : Nat := 512996613399150928155421

theorem tailTrace_2997172 : CollatzResearch.WordTrace tailWord_2997172 prefixEnd_2997172 512996613399150928155421 := by
  unfold tailWord_2997172
  simp only [CollatzResearch.WordTrace]
  refine ⟨54657921748882597535080885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72877228998510130046774513 54657921748882597535080885)
  ·
    refine ⟨5124180163957743518913833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54657921748882597535080885 5124180163957743518913833)
    ·
      refine ⟨3843135122968307639185375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5124180163957743518913833 3843135122968307639185375)
      ·
        refine ⟨5764702684452461458778063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843135122968307639185375 5764702684452461458778063)
        ·
          refine ⟨8647054026678692188167095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764702684452461458778063 8647054026678692188167095)
          ·
            refine ⟨12970581040018038282250643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8647054026678692188167095 12970581040018038282250643)
            ·
              refine ⟨19455871560027057423375965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12970581040018038282250643 19455871560027057423375965)
              ·
                refine ⟨7295951835010146533765987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19455871560027057423375965 7295951835010146533765987)
                ·
                  refine ⟨10943927752515219800648981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295951835010146533765987 10943927752515219800648981)
                  ·
                    refine ⟨512996613399150928155421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10943927752515219800648981 512996613399150928155421)
                    ·
                      rfl

theorem cell23_2997172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2997172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997172 prefixEnd_2997172 := by exact prefixLift 2997172
  have htrace : WordTrace (prefixWord ++ tailWord_2997172) baseStart_2997172 baseEnd_2997172 := by
    simpa [prefixWord, tailWord_2997172, baseEnd_2997172] using wordTrace_append hprefix tailTrace_2997172
  have hstable : (prefixWord ++ tailWord_2997172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997172).length < 2 ^ (prefixWord ++ tailWord_2997172).sum := by decide
  have hdescent : baseEnd_2997172 < baseStart_2997172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997182 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2997182 : Nat := 118140960795 + 2997182 * 2 ^ 59
def prefixEnd_2997182 : Nat := 4983230072969 + 3 ^ 40 * 2997182 * 2
def baseEnd_2997182 : Nat := 1538994975003997745341217

theorem tailTrace_2997182 : CollatzResearch.WordTrace tailWord_2997182 prefixEnd_2997182 1538994975003997745341217 := by
  unfold tailWord_2997182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13664526028466120847253225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72877472151819311185350533 13664526028466120847253225)
  ·
    refine ⟨10248394521349590635439919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13664526028466120847253225 10248394521349590635439919)
    ·
      refine ⟨15372591782024385953159879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10248394521349590635439919 15372591782024385953159879)
      ·
        refine ⟨23058887673036578929739819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15372591782024385953159879 23058887673036578929739819)
        ·
          refine ⟨34588331509554868394609729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23058887673036578929739819 34588331509554868394609729)
          ·
            refine ⟨25941248632166151295957297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34588331509554868394609729 25941248632166151295957297)
            ·
              refine ⟨19455936474124613471967973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25941248632166151295957297 19455936474124613471967973)
              ·
                refine ⟨3647988088898365025993995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19455936474124613471967973 3647988088898365025993995)
                ·
                  refine ⟨5471982133347547538990993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647988088898365025993995 5471982133347547538990993)
                  ·
                    refine ⟨4103986600010660654243245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471982133347547538990993 4103986600010660654243245)
                    ·
                      refine ⟨1538994975003997745341217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4103986600010660654243245 1538994975003997745341217)
                      ·
                        rfl

theorem cell23_2997182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2997182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997182 prefixEnd_2997182 := by exact prefixLift 2997182
  have htrace : WordTrace (prefixWord ++ tailWord_2997182) baseStart_2997182 baseEnd_2997182 := by
    simpa [prefixWord, tailWord_2997182, baseEnd_2997182] using wordTrace_append hprefix tailTrace_2997182
  have hstable : (prefixWord ++ tailWord_2997182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997182).length < 2 ^ (prefixWord ++ tailWord_2997182).sum := by decide
  have hdescent : baseEnd_2997182 < baseStart_2997182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997195 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 3]
def baseStart_2997195 : Nat := 118140960795 + 2997195 * 2 ^ 59
def prefixEnd_2997195 : Nat := 4983230072969 + 3 ^ 40 * 2997195 * 2
def baseEnd_2997195 : Nat := 1539001650252506194478657

theorem tailTrace_2997195 : CollatzResearch.WordTrace tailWord_2997195 prefixEnd_2997195 1539001650252506194478657 := by
  unfold tailWord_2997195
  simp only [CollatzResearch.WordTrace]
  refine ⟨109316682376681869998249039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72877788251121246665499359 109316682376681869998249039)
  ·
    refine ⟨163975023565022804997373559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109316682376681869998249039 163975023565022804997373559)
    ·
      refine ⟨245962535347534207496060339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163975023565022804997373559 245962535347534207496060339)
      ·
        refine ⟨368943803021301311244090509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245962535347534207496060339 368943803021301311244090509)
        ·
          refine ⟨138353926132987991716533941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368943803021301311244090509 138353926132987991716533941)
          ·
            refine ⟨12970680574967624223425057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138353926132987991716533941 12970680574967624223425057)
            ·
              refine ⟨9728010431225718167568793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12970680574967624223425057 9728010431225718167568793)
              ·
                refine ⟨7296007823419288625676595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9728010431225718167568793 7296007823419288625676595)
                ·
                  refine ⟨10944011735128932938514893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7296007823419288625676595 10944011735128932938514893)
                  ·
                    refine ⟨4104004400673349851943085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10944011735128932938514893 4104004400673349851943085)
                    ·
                      refine ⟨1539001650252506194478657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104004400673349851943085 1539001650252506194478657)
                      ·
                        rfl

theorem cell23_2997195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 3].length) (baseStart_2997195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997195 prefixEnd_2997195 := by exact prefixLift 2997195
  have htrace : WordTrace (prefixWord ++ tailWord_2997195) baseStart_2997195 baseEnd_2997195 := by
    simpa [prefixWord, tailWord_2997195, baseEnd_2997195] using wordTrace_append hprefix tailTrace_2997195
  have hstable : (prefixWord ++ tailWord_2997195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997195).length < 2 ^ (prefixWord ++ tailWord_2997195).sum := by decide
  have hdescent : baseEnd_2997195 < baseStart_2997195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997196 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 1, 2, 2]
def baseStart_2997196 : Nat := 118140960795 + 2997196 * 2 ^ 59
def prefixEnd_2997196 : Nat := 4983230072969 + 3 ^ 40 * 2997196 * 2
def baseEnd_2997196 : Nat := 1539002163733160690566153

theorem tailTrace_2997196 : CollatzResearch.WordTrace tailWord_2997196 prefixEnd_2997196 1539002163733160690566153 := by
  unfold tailWord_2997196
  simp only [CollatzResearch.WordTrace]
  refine ⟨54658359424839123584517721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72877812566452164779356961 54658359424839123584517721)
  ·
    refine ⟨40993769568629342688388291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54658359424839123584517721 40993769568629342688388291)
    ·
      refine ⟨61490654352944014032582437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40993769568629342688388291 61490654352944014032582437)
      ·
        refine ⟨11529497691177002631109207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61490654352944014032582437 11529497691177002631109207)
        ·
          refine ⟨17294246536765503946663811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11529497691177002631109207 17294246536765503946663811)
          ·
            refine ⟨25941369805148255919995717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17294246536765503946663811 25941369805148255919995717)
            ·
              refine ⟨4864006838465297984999197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25941369805148255919995717 4864006838465297984999197)
              ·
                refine ⟨1824002564424486744374699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4864006838465297984999197 1824002564424486744374699)
                ·
                  refine ⟨2736003846636730116562049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824002564424486744374699 2736003846636730116562049)
                  ·
                    refine ⟨2052002884977547587421537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2736003846636730116562049 2052002884977547587421537)
                    ·
                      refine ⟨1539002163733160690566153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052002884977547587421537 1539002163733160690566153)
                      ·
                        rfl

theorem cell23_2997196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_2997196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997196 prefixEnd_2997196 := by exact prefixLift 2997196
  have htrace : WordTrace (prefixWord ++ tailWord_2997196) baseStart_2997196 baseEnd_2997196 := by
    simpa [prefixWord, tailWord_2997196, baseEnd_2997196] using wordTrace_append hprefix tailTrace_2997196
  have hstable : (prefixWord ++ tailWord_2997196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997196).length < 2 ^ (prefixWord ++ tailWord_2997196).sum := by decide
  have hdescent : baseEnd_2997196 < baseStart_2997196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997199 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 1, 2, 3]
def baseStart_2997199 : Nat := 118140960795 + 2997199 * 2 ^ 59
def prefixEnd_2997199 : Nat := 4983230072969 + 3 ^ 40 * 2997199 * 2
def baseEnd_2997199 : Nat := 1539003704175124178828639

theorem tailTrace_2997199 : CollatzResearch.WordTrace tailWord_2997199 prefixEnd_2997199 1539003704175124178828639 := by
  unfold tailWord_2997199
  simp only [CollatzResearch.WordTrace]
  refine ⟨109316828268667378681394651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72877885512444919120929767 109316828268667378681394651)
  ·
    refine ⟨163975242403001068022091977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109316828268667378681394651 163975242403001068022091977)
    ·
      refine ⟨122981431802250801016568983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163975242403001068022091977 122981431802250801016568983)
      ·
        refine ⟨184472147703376201524853475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122981431802250801016568983 184472147703376201524853475)
        ·
          refine ⟨276708221555064302287280213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184472147703376201524853475 276708221555064302287280213)
          ·
            refine ⟨3242674471348409792429065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 276708221555064302287280213 3242674471348409792429065)
            ·
              refine ⟨2432005853511307344321799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242674471348409792429065 2432005853511307344321799)
              ·
                refine ⟨3648008780266961016482699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432005853511307344321799 3648008780266961016482699)
                ·
                  refine ⟨5472013170400441524724049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648008780266961016482699 5472013170400441524724049)
                  ·
                    refine ⟨4104009877800331143543037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5472013170400441524724049 4104009877800331143543037)
                    ·
                      refine ⟨1539003704175124178828639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104009877800331143543037 1539003704175124178828639)
                      ·
                        rfl

theorem cell23_2997199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 2, 3].length) (baseStart_2997199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997199 prefixEnd_2997199 := by exact prefixLift 2997199
  have htrace : WordTrace (prefixWord ++ tailWord_2997199) baseStart_2997199 baseEnd_2997199 := by
    simpa [prefixWord, tailWord_2997199, baseEnd_2997199] using wordTrace_append hprefix tailTrace_2997199
  have hstable : (prefixWord ++ tailWord_2997199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997199).length < 2 ^ (prefixWord ++ tailWord_2997199).sum := by decide
  have hdescent : baseEnd_2997199 < baseStart_2997199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997206 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_2997206 : Nat := 118140960795 + 2997206 * 2 ^ 59
def prefixEnd_2997206 : Nat := 4983230072969 + 3 ^ 40 * 2997206 * 2
def baseEnd_2997206 : Nat := 513002432846568550480369

theorem tailTrace_2997206 : CollatzResearch.WordTrace tailWord_2997206 prefixEnd_2997206 513002432846568550480369 := by
  unfold tailWord_2997206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6832317723727626179806217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72878055719761345917932981 6832317723727626179806217)
  ·
    refine ⟨5124238292795719634854663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6832317723727626179806217 5124238292795719634854663)
    ·
      refine ⟨7686357439193579452281995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5124238292795719634854663 7686357439193579452281995)
      ·
        refine ⟨11529536158790369178422993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686357439193579452281995 11529536158790369178422993)
        ·
          refine ⟨8647152119092776883817245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11529536158790369178422993 8647152119092776883817245)
          ·
            refine ⟨3242682044659791331431467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8647152119092776883817245 3242682044659791331431467)
            ·
              refine ⟨4864023066989686997147201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242682044659791331431467 4864023066989686997147201)
              ·
                refine ⟨3648017300242265247860401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864023066989686997147201 3648017300242265247860401)
                ·
                  refine ⟨2736012975181698935895301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3648017300242265247860401 2736012975181698935895301)
                  ·
                    refine ⟨513002432846568550480369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2736012975181698935895301 513002432846568550480369)
                    ·
                      rfl

theorem cell23_2997206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_2997206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997206 prefixEnd_2997206 := by exact prefixLift 2997206
  have htrace : WordTrace (prefixWord ++ tailWord_2997206) baseStart_2997206 baseEnd_2997206 := by
    simpa [prefixWord, tailWord_2997206, baseEnd_2997206] using wordTrace_append hprefix tailTrace_2997206
  have hstable : (prefixWord ++ tailWord_2997206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997206).length < 2 ^ (prefixWord ++ tailWord_2997206).sum := by decide
  have hdescent : baseEnd_2997206 < baseStart_2997206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997236 : List Nat := [2, 6, 2, 1, 1, 1, 1, 9]
def baseStart_2997236 : Nat := 118140960795 + 2997236 * 2 ^ 59
def prefixEnd_2997236 : Nat := 4983230072969 + 3 ^ 40 * 2997236 * 2
def baseEnd_2997236 : Nat := 57000840850345945706147

theorem tailTrace_2997236 : CollatzResearch.WordTrace tailWord_2997236 prefixEnd_2997236 57000840850345945706147 := by
  unfold tailWord_2997236
  simp only [CollatzResearch.WordTrace]
  refine ⟨54659088884766667000245781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72878785179688889333661041 54659088884766667000245781)
  ·
    refine ⟨2562144791473437515636521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54659088884766667000245781 2562144791473437515636521)
    ·
      refine ⟨1921608593605078136727391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2562144791473437515636521 1921608593605078136727391)
      ·
        refine ⟨2882412890407617205091087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921608593605078136727391 2882412890407617205091087)
        ·
          refine ⟨4323619335611425807636631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882412890407617205091087 4323619335611425807636631)
          ·
            refine ⟨6485429003417138711454947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323619335611425807636631 6485429003417138711454947)
            ·
              refine ⟨9728143505125708067182421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6485429003417138711454947 9728143505125708067182421)
              ·
                refine ⟨57000840850345945706147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9728143505125708067182421 57000840850345945706147)
                ·
                  rfl

theorem cell23_2997236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 9].length) (baseStart_2997236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997236 prefixEnd_2997236 := by exact prefixLift 2997236
  have htrace : WordTrace (prefixWord ++ tailWord_2997236) baseStart_2997236 baseEnd_2997236 := by
    simpa [prefixWord, tailWord_2997236, baseEnd_2997236] using wordTrace_append hprefix tailTrace_2997236
  have hstable : (prefixWord ++ tailWord_2997236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997236).length < 2 ^ (prefixWord ++ tailWord_2997236).sum := by decide
  have hdescent : baseEnd_2997236 < baseStart_2997236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997255 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2997255 : Nat := 118140960795 + 2997255 * 2 ^ 59
def prefixEnd_2997255 : Nat := 4983230072969 + 3 ^ 40 * 2997255 * 2
def baseEnd_2997255 : Nat := 1539032459091775959728381

theorem tailTrace_2997255 : CollatzResearch.WordTrace tailWord_2997255 prefixEnd_2997255 1539032459091775959728381 := by
  unfold tailWord_2997255
  simp only [CollatzResearch.WordTrace]
  refine ⟨109318870756464500245433219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72879247170976333496955479 109318870756464500245433219)
  ·
    refine ⟨163978306134696750368149829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109318870756464500245433219 163978306134696750368149829)
    ·
      refine ⟨30745932400255640694028093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163978306134696750368149829 30745932400255640694028093)
      ·
        refine ⟨11529724650095865260260535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30745932400255640694028093 11529724650095865260260535)
        ·
          refine ⟨17294586975143797890390803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11529724650095865260260535 17294586975143797890390803)
          ·
            refine ⟨25941880462715696835586205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17294586975143797890390803 25941880462715696835586205)
            ·
              refine ⟨9728205173518386313344827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25941880462715696835586205 9728205173518386313344827)
              ·
                refine ⟨14592307760277579470017241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9728205173518386313344827 14592307760277579470017241)
                ·
                  refine ⟨10944230820208184602512931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14592307760277579470017241 10944230820208184602512931)
                  ·
                    refine ⟨16416346230312276903769397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10944230820208184602512931 16416346230312276903769397)
                    ·
                      refine ⟨1539032459091775959728381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16416346230312276903769397 1539032459091775959728381)
                      ·
                        rfl

theorem cell23_2997255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2997255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997255 prefixEnd_2997255 := by exact prefixLift 2997255
  have htrace : WordTrace (prefixWord ++ tailWord_2997255) baseStart_2997255 baseEnd_2997255 := by
    simpa [prefixWord, tailWord_2997255, baseEnd_2997255] using wordTrace_append hprefix tailTrace_2997255
  have hstable : (prefixWord ++ tailWord_2997255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997255).length < 2 ^ (prefixWord ++ tailWord_2997255).sum := by decide
  have hdescent : baseEnd_2997255 < baseStart_2997255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997269 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_2997269 : Nat := 118140960795 + 2997269 * 2 ^ 59
def prefixEnd_2997269 : Nat := 4983230072969 + 3 ^ 40 * 2997269 * 2
def baseEnd_2997269 : Nat := 1539039647820938904953317

theorem tailTrace_2997269 : CollatzResearch.WordTrace tailWord_2997269 prefixEnd_2997269 1539039647820938904953317 := by
  unfold tailWord_2997269
  simp only [CollatzResearch.WordTrace]
  refine ⟨109319381378413780636442861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72879587585609187090961907 109319381378413780636442861)
  ·
    refine ⟨40994768016905167738666073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109319381378413780636442861 40994768016905167738666073)
    ·
      refine ⟨30746076012678875803999555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40994768016905167738666073 30746076012678875803999555)
      ·
        refine ⟨46119114019018313705999333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30746076012678875803999555 46119114019018313705999333)
        ·
          refine ⟨8647333878565933819874875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46119114019018313705999333 8647333878565933819874875)
          ·
            refine ⟨12971000817848900729812313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8647333878565933819874875 12971000817848900729812313)
            ·
              refine ⟨9728250613386675547359235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12971000817848900729812313 9728250613386675547359235)
              ·
                refine ⟨14592375920080013321038853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9728250613386675547359235 14592375920080013321038853)
                ·
                  refine ⟨2736070485015002497694785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14592375920080013321038853 2736070485015002497694785)
                  ·
                    refine ⟨2052052863761251873271089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2736070485015002497694785 2052052863761251873271089)
                    ·
                      refine ⟨1539039647820938904953317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052052863761251873271089 1539039647820938904953317)
                      ·
                        rfl

theorem cell23_2997269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_2997269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997269 prefixEnd_2997269 := by exact prefixLift 2997269
  have htrace : WordTrace (prefixWord ++ tailWord_2997269) baseStart_2997269 baseEnd_2997269 := by
    simpa [prefixWord, tailWord_2997269, baseEnd_2997269] using wordTrace_append hprefix tailTrace_2997269
  have hstable : (prefixWord ++ tailWord_2997269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997269).length < 2 ^ (prefixWord ++ tailWord_2997269).sum := by decide
  have hdescent : baseEnd_2997269 < baseStart_2997269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997280 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2997280 : Nat := 118140960795 + 2997280 * 2 ^ 59
def prefixEnd_2997280 : Nat := 4983230072969 + 3 ^ 40 * 2997280 * 2
def baseEnd_2997280 : Nat := 1539045296108138361915767

theorem tailTrace_2997280 : CollatzResearch.WordTrace tailWord_2997280 prefixEnd_2997280 1539045296108138361915767 := by
  unfold tailWord_2997280
  simp only [CollatzResearch.WordTrace]
  refine ⟨54659891290686964757546647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72879855054249286343395529 54659891290686964757546647)
  ·
    refine ⟨81989836936030447136319971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54659891290686964757546647 81989836936030447136319971)
    ·
      refine ⟨122984755404045670704479957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81989836936030447136319971 122984755404045670704479957)
      ·
        refine ⟨2882455204782320407136249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 122984755404045670704479957 2882455204782320407136249)
        ·
          refine ⟨2161841403586740305352187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2882455204782320407136249 2161841403586740305352187)
          ·
            refine ⟨3242762105380110458028281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161841403586740305352187 3242762105380110458028281)
            ·
              refine ⟨2432071579035082843521211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242762105380110458028281 2432071579035082843521211)
              ·
                refine ⟨3648107368552624265281817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432071579035082843521211 3648107368552624265281817)
                ·
                  refine ⟨2736080526414468198961363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3648107368552624265281817 2736080526414468198961363)
                  ·
                    refine ⟨4104120789621702298442045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736080526414468198961363 4104120789621702298442045)
                    ·
                      refine ⟨1539045296108138361915767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104120789621702298442045 1539045296108138361915767)
                      ·
                        rfl

theorem cell23_2997280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2997280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997280 prefixEnd_2997280 := by exact prefixLift 2997280
  have htrace : WordTrace (prefixWord ++ tailWord_2997280) baseStart_2997280 baseEnd_2997280 := by
    simpa [prefixWord, tailWord_2997280, baseEnd_2997280] using wordTrace_append hprefix tailTrace_2997280
  have hstable : (prefixWord ++ tailWord_2997280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997280).length < 2 ^ (prefixWord ++ tailWord_2997280).sum := by decide
  have hdescent : baseEnd_2997280 < baseStart_2997280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997285 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_2997285 : Nat := 118140960795 + 2997285 * 2 ^ 59
def prefixEnd_2997285 : Nat := 4983230072969 + 3 ^ 40 * 2997285 * 2
def baseEnd_2997285 : Nat := 1539047863511410842353243

theorem tailTrace_2997285 : CollatzResearch.WordTrace tailWord_2997285 prefixEnd_2997285 1539047863511410842353243 := by
  unfold tailWord_2997285
  simp only [CollatzResearch.WordTrace]
  refine ⟨109319964946355815369025309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72879976630903876912683539 109319964946355815369025309)
  ·
    refine ⟨40994986854883430763384491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109319964946355815369025309 40994986854883430763384491)
    ·
      refine ⟨61492480282325146145076737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40994986854883430763384491 61492480282325146145076737)
      ·
        refine ⟨46119360211743859608807553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61492480282325146145076737 46119360211743859608807553)
        ·
          refine ⟨34589520158807894706605665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46119360211743859608807553 34589520158807894706605665)
          ·
            refine ⟨25942140119105921029954249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34589520158807894706605665 25942140119105921029954249)
            ·
              refine ⟨19456605089329440772465687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25942140119105921029954249 19456605089329440772465687)
              ·
                refine ⟨29184907633994161158698531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19456605089329440772465687 29184907633994161158698531)
                ·
                  refine ⟨43777361450991241738047797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29184907633994161158698531 43777361450991241738047797)
                  ·
                    refine ⟨4104127636030428912941981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43777361450991241738047797 4104127636030428912941981)
                    ·
                      refine ⟨1539047863511410842353243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104127636030428912941981 1539047863511410842353243)
                      ·
                        rfl

theorem cell23_2997285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_2997285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997285 prefixEnd_2997285 := by exact prefixLift 2997285
  have htrace : WordTrace (prefixWord ++ tailWord_2997285) baseStart_2997285 baseEnd_2997285 := by
    simpa [prefixWord, tailWord_2997285, baseEnd_2997285] using wordTrace_append hprefix tailTrace_2997285
  have hstable : (prefixWord ++ tailWord_2997285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997285).length < 2 ^ (prefixWord ++ tailWord_2997285).sum := by decide
  have hdescent : baseEnd_2997285 < baseStart_2997285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997362 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2997362 : Nat := 118140960795 + 2997362 * 2 ^ 59
def prefixEnd_2997362 : Nat := 4983230072969 + 3 ^ 40 * 2997362 * 2
def baseEnd_2997362 : Nat := 1539087401521807041090389

theorem tailTrace_2997362 : CollatzResearch.WordTrace tailWord_2997362 prefixEnd_2997362 1539087401521807041090389 := by
  unfold tailWord_2997362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27330693341769214379894585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72881848911384571679718893 27330693341769214379894585)
  ·
    refine ⟨20498020006326910784920939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27330693341769214379894585 20498020006326910784920939)
    ·
      refine ⟨30747030009490366177381409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20498020006326910784920939 30747030009490366177381409)
      ·
        refine ⟨23060272507117774633036057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30747030009490366177381409 23060272507117774633036057)
        ·
          refine ⟨17295204380338330974777043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23060272507117774633036057 17295204380338330974777043)
          ·
            refine ⟨25942806570507496462165565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17295204380338330974777043 25942806570507496462165565)
            ·
              refine ⟨9728552463940311173312087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25942806570507496462165565 9728552463940311173312087)
              ·
                refine ⟨14592828695910466759968131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9728552463940311173312087 14592828695910466759968131)
                ·
                  refine ⟨21889243043865700139952197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14592828695910466759968131 21889243043865700139952197)
                  ·
                    refine ⟨4104233070724818776241037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21889243043865700139952197 4104233070724818776241037)
                    ·
                      refine ⟨1539087401521807041090389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104233070724818776241037 1539087401521807041090389)
                      ·
                        rfl

theorem cell23_2997362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2997362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997362 prefixEnd_2997362 := by exact prefixLift 2997362
  have htrace : WordTrace (prefixWord ++ tailWord_2997362) baseStart_2997362 baseEnd_2997362 := by
    simpa [prefixWord, tailWord_2997362, baseEnd_2997362] using wordTrace_append hprefix tailTrace_2997362
  have hstable : (prefixWord ++ tailWord_2997362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997362).length < 2 ^ (prefixWord ++ tailWord_2997362).sum := by decide
  have hdescent : baseEnd_2997362 < baseStart_2997362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997375 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_2997375 : Nat := 118140960795 + 2997375 * 2 ^ 59
def prefixEnd_2997375 : Nat := 4983230072969 + 3 ^ 40 * 2997375 * 2
def baseEnd_2997375 : Nat := 1539094076770315490227829

theorem tailTrace_2997375 : CollatzResearch.WordTrace tailWord_2997375 prefixEnd_2997375 1539094076770315490227829 := by
  unfold tailWord_2997375
  simp only [CollatzResearch.WordTrace]
  refine ⟨109323247516029760739801579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72882165010686507159867719 109323247516029760739801579)
  ·
    refine ⟨163984871274044641109702369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109323247516029760739801579 163984871274044641109702369)
    ·
      refine ⟨122988653455533480832276777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163984871274044641109702369 122988653455533480832276777)
      ·
        refine ⟨92241490091650110624207583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122988653455533480832276777 92241490091650110624207583)
        ·
          refine ⟨138362235137475165936311375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92241490091650110624207583 138362235137475165936311375)
          ·
            refine ⟨207543352706212748904467063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138362235137475165936311375 207543352706212748904467063)
            ·
              refine ⟨311315029059319123356700595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207543352706212748904467063 311315029059319123356700595)
              ·
                refine ⟨466972543588978685035050893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311315029059319123356700595 466972543588978685035050893)
                ·
                  refine ⟨175114703845867006888144085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466972543588978685035050893 175114703845867006888144085)
                  ·
                    refine ⟨4104250871387507973940877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175114703845867006888144085 4104250871387507973940877)
                    ·
                      refine ⟨1539094076770315490227829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104250871387507973940877 1539094076770315490227829)
                      ·
                        rfl

theorem cell23_2997375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_2997375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997375 prefixEnd_2997375 := by exact prefixLift 2997375
  have htrace : WordTrace (prefixWord ++ tailWord_2997375) baseStart_2997375 baseEnd_2997375 := by
    simpa [prefixWord, tailWord_2997375, baseEnd_2997375] using wordTrace_append hprefix tailTrace_2997375
  have hstable : (prefixWord ++ tailWord_2997375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997375).length < 2 ^ (prefixWord ++ tailWord_2997375).sum := by decide
  have hdescent : baseEnd_2997375 < baseStart_2997375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997385 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_2997385 : Nat := 118140960795 + 2997385 * 2 ^ 59
def prefixEnd_2997385 : Nat := 4983230072969 + 3 ^ 40 * 2997385 * 2
def baseEnd_2997385 : Nat := 1539099211576860451102783

theorem tailTrace_2997385 : CollatzResearch.WordTrace tailWord_2997385 prefixEnd_2997385 1539099211576860451102783 := by
  unfold tailWord_2997385
  simp only [CollatzResearch.WordTrace]
  refine ⟨109323612245993532447665609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72882408163995688298443739 109323612245993532447665609)
  ·
    refine ⟨81992709184495149335749207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109323612245993532447665609 81992709184495149335749207)
    ·
      refine ⟨122989063776742724003623811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81992709184495149335749207 122989063776742724003623811)
      ·
        refine ⟨184483595665114086005435717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122989063776742724003623811 184483595665114086005435717)
        ·
          refine ⟨34590674187208891126019197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184483595665114086005435717 34590674187208891126019197)
          ·
            refine ⟨12971502820203334172257199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34590674187208891126019197 12971502820203334172257199)
            ·
              refine ⟨19457254230305001258385799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12971502820203334172257199 19457254230305001258385799)
              ·
                refine ⟨29185881345457501887578699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19457254230305001258385799 29185881345457501887578699)
                ·
                  refine ⟨43778822018186252831368049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29185881345457501887578699 43778822018186252831368049)
                  ·
                    refine ⟨32834116513639689623526037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43778822018186252831368049 32834116513639689623526037)
                    ·
                      refine ⟨1539099211576860451102783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32834116513639689623526037 1539099211576860451102783)
                      ·
                        rfl

theorem cell23_2997385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_2997385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997385 prefixEnd_2997385 := by exact prefixLift 2997385
  have htrace : WordTrace (prefixWord ++ tailWord_2997385) baseStart_2997385 baseEnd_2997385 := by
    simpa [prefixWord, tailWord_2997385, baseEnd_2997385] using wordTrace_append hprefix tailTrace_2997385
  have hstable : (prefixWord ++ tailWord_2997385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997385).length < 2 ^ (prefixWord ++ tailWord_2997385).sum := by decide
  have hdescent : baseEnd_2997385 < baseStart_2997385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997395 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 5, 5]
def baseStart_2997395 : Nat := 118140960795 + 2997395 * 2 ^ 59
def prefixEnd_2997395 : Nat := 4983230072969 + 3 ^ 40 * 2997395 * 2
def baseEnd_2997395 : Nat := 513034782127801803992579

theorem tailTrace_2997395 : CollatzResearch.WordTrace tailWord_2997395 prefixEnd_2997395 513034782127801803992579 := by
  unfold tailWord_2997395
  simp only [CollatzResearch.WordTrace]
  refine ⟨109323976975957304155529639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72882651317304869437019759 109323976975957304155529639)
  ·
    refine ⟨163985965463935956233294459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109323976975957304155529639 163985965463935956233294459)
    ·
      refine ⟨245978948195903934349941689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163985965463935956233294459 245978948195903934349941689)
      ·
        refine ⟨184484211146927950762456267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245978948195903934349941689 184484211146927950762456267)
        ·
          refine ⟨276726316720391926143684401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184484211146927950762456267 276726316720391926143684401)
          ·
            refine ⟨207544737540293944607763301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276726316720391926143684401 207544737540293944607763301)
            ·
              refine ⟨38914638288805114613955619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207544737540293944607763301 38914638288805114613955619)
              ·
                refine ⟨58371957433207671920933429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38914638288805114613955619 58371957433207671920933429)
                ·
                  refine ⟨5472371009363219242587509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58371957433207671920933429 5472371009363219242587509)
                  ·
                    refine ⟨513034782127801803992579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5472371009363219242587509 513034782127801803992579)
                    ·
                      rfl

theorem cell23_2997395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 5].length) (baseStart_2997395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997395 prefixEnd_2997395 := by exact prefixLift 2997395
  have htrace : WordTrace (prefixWord ++ tailWord_2997395) baseStart_2997395 baseEnd_2997395 := by
    simpa [prefixWord, tailWord_2997395, baseEnd_2997395] using wordTrace_append hprefix tailTrace_2997395
  have hstable : (prefixWord ++ tailWord_2997395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997395).length < 2 ^ (prefixWord ++ tailWord_2997395).sum := by decide
  have hdescent : baseEnd_2997395 < baseStart_2997395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997399 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 6]
def baseStart_2997399 : Nat := 118140960795 + 2997399 * 2 ^ 59
def prefixEnd_2997399 : Nat := 4983230072969 + 3 ^ 40 * 2997399 * 2
def baseEnd_2997399 : Nat := 171011822256224821814191

theorem tailTrace_2997399 : CollatzResearch.WordTrace tailWord_2997399 prefixEnd_2997399 171011822256224821814191 := by
  unfold tailWord_2997399
  simp only [CollatzResearch.WordTrace]
  refine ⟨109324122867942812838675251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72882748578628541892450167 109324122867942812838675251)
  ·
    refine ⟨163986184301914219258012877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109324122867942812838675251 163986184301914219258012877)
    ·
      refine ⟨61494819113217832221754829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163986184301914219258012877 61494819113217832221754829)
      ·
        refine ⟨23060557167456687083158061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61494819113217832221754829 23060557167456687083158061)
        ·
          refine ⟨8647708937796257656184273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23060557167456687083158061 8647708937796257656184273)
          ·
            refine ⟨6485781703347193242138205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8647708937796257656184273 6485781703347193242138205)
            ·
              refine ⟨2432168138755197465801827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6485781703347193242138205 2432168138755197465801827)
              ·
                refine ⟨3648252208132796198702741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432168138755197465801827 3648252208132796198702741)
                ·
                  refine ⟨171011822256224821814191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3648252208132796198702741 171011822256224821814191)
                  ·
                    rfl

theorem cell23_2997399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 6].length) (baseStart_2997399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997399 prefixEnd_2997399 := by exact prefixLift 2997399
  have htrace : WordTrace (prefixWord ++ tailWord_2997399) baseStart_2997399 baseEnd_2997399 := by
    simpa [prefixWord, tailWord_2997399, baseEnd_2997399] using wordTrace_append hprefix tailTrace_2997399
  have hstable : (prefixWord ++ tailWord_2997399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997399).length < 2 ^ (prefixWord ++ tailWord_2997399).sum := by decide
  have hdescent : baseEnd_2997399 < baseStart_2997399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997409 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2997409 : Nat := 118140960795 + 2997409 * 2 ^ 59
def prefixEnd_2997409 : Nat := 4983230072969 + 3 ^ 40 * 2997409 * 2
def baseEnd_2997409 : Nat := 1539111535112568357202673

theorem tailTrace_2997409 : CollatzResearch.WordTrace tailWord_2997409 prefixEnd_2997409 1539111535112568357202673 := by
  unfold tailWord_2997409
  simp only [CollatzResearch.WordTrace]
  refine ⟨109324487597906584546539281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72882991731937723031026187 109324487597906584546539281)
  ·
    refine ⟨81993365698429938409904461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109324487597906584546539281 81993365698429938409904461)
    ·
      refine ⟨30747512136911226903714173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81993365698429938409904461 30747512136911226903714173)
      ·
        refine ⟨11530317051341710088892815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30747512136911226903714173 11530317051341710088892815)
        ·
          refine ⟨17295475577012565133339223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11530317051341710088892815 17295475577012565133339223)
          ·
            refine ⟨25943213365518847700008835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17295475577012565133339223 25943213365518847700008835)
            ·
              refine ⟨38914820048278271550013253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25943213365518847700008835 38914820048278271550013253)
              ·
                refine ⟨7296528759052175915627485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38914820048278271550013253 7296528759052175915627485)
                ·
                  refine ⟨2736198284644565968360307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7296528759052175915627485 2736198284644565968360307)
                  ·
                    refine ⟨4104297426966848952540461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736198284644565968360307 4104297426966848952540461)
                    ·
                      refine ⟨1539111535112568357202673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104297426966848952540461 1539111535112568357202673)
                      ·
                        rfl

theorem cell23_2997409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2997409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997409 prefixEnd_2997409 := by exact prefixLift 2997409
  have htrace : WordTrace (prefixWord ++ tailWord_2997409) baseStart_2997409 baseEnd_2997409 := by
    simpa [prefixWord, tailWord_2997409, baseEnd_2997409] using wordTrace_append hprefix tailTrace_2997409
  have hstable : (prefixWord ++ tailWord_2997409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997409).length < 2 ^ (prefixWord ++ tailWord_2997409).sum := by decide
  have hdescent : baseEnd_2997409 < baseStart_2997409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997436 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2997436 : Nat := 118140960795 + 2997436 * 2 ^ 59
def prefixEnd_2997436 : Nat := 4983230072969 + 3 ^ 40 * 2997436 * 2
def baseEnd_2997436 : Nat := 1539125399090239751565049

theorem tailTrace_2997436 : CollatzResearch.WordTrace tailWord_2997436 prefixEnd_2997436 1539125399090239751565049 := by
  unfold tailWord_2997436
  simp only [CollatzResearch.WordTrace]
  refine ⟨54662736184404384078886081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72883648245872512105181441 54662736184404384078886081)
  ·
    refine ⟨40997052138303288059164561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54662736184404384078886081 40997052138303288059164561)
    ·
      refine ⟨30747789103727466044373421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40997052138303288059164561 30747789103727466044373421)
      ·
        refine ⟨11530420913897799766640033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30747789103727466044373421 11530420913897799766640033)
        ·
          refine ⟨8647815685423349824980025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11530420913897799766640033 8647815685423349824980025)
          ·
            refine ⟨6485861764067512368735019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8647815685423349824980025 6485861764067512368735019)
            ·
              refine ⟨9728792646101268553102529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6485861764067512368735019 9728792646101268553102529)
              ·
                refine ⟨7296594484575951414826897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9728792646101268553102529 7296594484575951414826897)
                ·
                  refine ⟨5472445863431963561120173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7296594484575951414826897 5472445863431963561120173)
                  ·
                    refine ⟨2052167198786986335420065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5472445863431963561120173 2052167198786986335420065)
                    ·
                      refine ⟨1539125399090239751565049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052167198786986335420065 1539125399090239751565049)
                      ·
                        rfl

theorem cell23_2997436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2997436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997436 prefixEnd_2997436 := by exact prefixLift 2997436
  have htrace : WordTrace (prefixWord ++ tailWord_2997436) baseStart_2997436 baseEnd_2997436 := by
    simpa [prefixWord, tailWord_2997436, baseEnd_2997436] using wordTrace_append hprefix tailTrace_2997436
  have hstable : (prefixWord ++ tailWord_2997436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997436).length < 2 ^ (prefixWord ++ tailWord_2997436).sum := by decide
  have hdescent : baseEnd_2997436 < baseStart_2997436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997500 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_2997500 : Nat := 118140960795 + 2997500 * 2 ^ 59
def prefixEnd_2997500 : Nat := 4983230072969 + 3 ^ 40 * 2997500 * 2
def baseEnd_2997500 : Nat := 1539158261852127501164755

theorem tailTrace_2997500 : CollatzResearch.WordTrace tailWord_2997500 prefixEnd_2997500 1539158261852127501164755 := by
  unfold tailWord_2997500
  simp only [CollatzResearch.WordTrace]
  refine ⟨54663903320288453544050977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72885204427051271392067969 54663903320288453544050977)
  ·
    refine ⟨40997927490216340158038233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54663903320288453544050977 40997927490216340158038233)
    ·
      refine ⟨30748445617662255118528675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40997927490216340158038233 30748445617662255118528675)
      ·
        refine ⟨46122668426493382677793013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30748445617662255118528675 46122668426493382677793013)
        ·
          refine ⟨4324000164983754626043095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46122668426493382677793013 4324000164983754626043095)
          ·
            refine ⟨6486000247475631939064643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324000164983754626043095 6486000247475631939064643)
            ·
              refine ⟨9729000371213447908596965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486000247475631939064643 9729000371213447908596965)
              ·
                refine ⟨1824187569602521482861931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9729000371213447908596965 1824187569602521482861931)
                ·
                  refine ⟨2736281354403782224292897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824187569602521482861931 2736281354403782224292897)
                  ·
                    refine ⟨2052211015802836668219673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2736281354403782224292897 2052211015802836668219673)
                    ·
                      refine ⟨1539158261852127501164755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052211015802836668219673 1539158261852127501164755)
                      ·
                        rfl

theorem cell23_2997500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_2997500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997500 prefixEnd_2997500 := by exact prefixLift 2997500
  have htrace : WordTrace (prefixWord ++ tailWord_2997500) baseStart_2997500 baseEnd_2997500 := by
    simpa [prefixWord, tailWord_2997500, baseEnd_2997500] using wordTrace_append hprefix tailTrace_2997500
  have hstable : (prefixWord ++ tailWord_2997500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997500).length < 2 ^ (prefixWord ++ tailWord_2997500).sum := by decide
  have hdescent : baseEnd_2997500 < baseStart_2997500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997506 : List Nat := [3, 4, 1, 1, 3, 2, 1, 8]
def baseStart_2997506 : Nat := 118140960795 + 2997506 * 2 ^ 59
def prefixEnd_2997506 : Nat := 4983230072969 + 3 ^ 40 * 2997506 * 2
def baseEnd_2997506 : Nat := 57005975656890906581101

theorem tailTrace_2997506 : CollatzResearch.WordTrace tailWord_2997506 prefixEnd_2997506 57005975656890906581101 := by
  unfold tailWord_2997506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27332006369638792528205093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72885350319036780075213581 27332006369638792528205093)
  ·
    refine ⟨5124751194307273599038455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27332006369638792528205093 5124751194307273599038455)
    ·
      refine ⟨7687126791460910398557683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5124751194307273599038455 7687126791460910398557683)
      ·
        refine ⟨11530690187191365597836525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7687126791460910398557683 11530690187191365597836525)
        ·
          refine ⟨4324008820196762099188697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11530690187191365597836525 4324008820196762099188697)
          ·
            refine ⟨3243006615147571574391523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324008820196762099188697 3243006615147571574391523)
            ·
              refine ⟨4864509922721357361587285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243006615147571574391523 4864509922721357361587285)
              ·
                refine ⟨57005975656890906581101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4864509922721357361587285 57005975656890906581101)
                ·
                  rfl

theorem cell23_2997506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_2997506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997506 prefixEnd_2997506 := by exact prefixLift 2997506
  have htrace : WordTrace (prefixWord ++ tailWord_2997506) baseStart_2997506 baseEnd_2997506 := by
    simpa [prefixWord, tailWord_2997506, baseEnd_2997506] using wordTrace_append hprefix tailTrace_2997506
  have hstable : (prefixWord ++ tailWord_2997506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997506).length < 2 ^ (prefixWord ++ tailWord_2997506).sum := by decide
  have hdescent : baseEnd_2997506 < baseStart_2997506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997509 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 5, 3, 2]
def baseStart_2997509 : Nat := 118140960795 + 2997509 * 2 ^ 59
def prefixEnd_2997509 : Nat := 4983230072969 + 3 ^ 40 * 2997509 * 2
def baseEnd_2997509 : Nat := 1539162883178017965952213

theorem tailTrace_2997509 : CollatzResearch.WordTrace tailWord_2997509 prefixEnd_2997509 1539162883178017965952213 := by
  unfold tailWord_2997509
  simp only [CollatzResearch.WordTrace]
  refine ⟨109328134897544301625179581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72885423265029534416786387 109328134897544301625179581)
  ·
    refine ⟨40998050586579113109442343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109328134897544301625179581 40998050586579113109442343)
    ·
      refine ⟨61497075879868669664163515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40998050586579113109442343 61497075879868669664163515)
      ·
        refine ⟨92245613819803004496245273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61497075879868669664163515 92245613819803004496245273)
        ·
          refine ⟨69184210364852253372183955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92245613819803004496245273 69184210364852253372183955)
          ·
            refine ⟨103776315547278380058275933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69184210364852253372183955 103776315547278380058275933)
            ·
              refine ⟨38916118330229392521853475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103776315547278380058275933 38916118330229392521853475)
              ·
                refine ⟨58374177495344088782780213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38916118330229392521853475 58374177495344088782780213)
                ·
                  refine ⟨5472579140188508323385645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58374177495344088782780213 5472579140188508323385645)
                  ·
                    refine ⟨2052217177570690621269617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5472579140188508323385645 2052217177570690621269617)
                    ·
                      refine ⟨1539162883178017965952213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052217177570690621269617 1539162883178017965952213)
                      ·
                        rfl

theorem cell23_2997509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_2997509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997509 prefixEnd_2997509 := by exact prefixLift 2997509
  have htrace : WordTrace (prefixWord ++ tailWord_2997509) baseStart_2997509 baseEnd_2997509 := by
    simpa [prefixWord, tailWord_2997509, baseEnd_2997509] using wordTrace_append hprefix tailTrace_2997509
  have hstable : (prefixWord ++ tailWord_2997509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997509).length < 2 ^ (prefixWord ++ tailWord_2997509).sum := by decide
  have hdescent : baseEnd_2997509 < baseStart_2997509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997516 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_2997516 : Nat := 118140960795 + 2997516 * 2 ^ 59
def prefixEnd_2997516 : Nat := 4983230072969 + 3 ^ 40 * 2997516 * 2
def baseEnd_2997516 : Nat := 1539166477542599438564681

theorem tailTrace_2997516 : CollatzResearch.WordTrace tailWord_2997516 prefixEnd_2997516 1539166477542599438564681 := by
  unfold tailWord_2997516
  simp only [CollatzResearch.WordTrace]
  refine ⟨54664195104259470910342201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72885593472345961213789601 54664195104259470910342201)
  ·
    refine ⟨40998146328194603182756651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54664195104259470910342201 40998146328194603182756651)
    ·
      refine ⟨61497219492291904774134977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40998146328194603182756651 61497219492291904774134977)
      ·
        refine ⟨46122914619218928580601233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61497219492291904774134977 46122914619218928580601233)
        ·
          refine ⟨34592185964414196435450925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46122914619218928580601233 34592185964414196435450925)
          ·
            refine ⟨12972069736655323663294097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34592185964414196435450925 12972069736655323663294097)
            ·
              refine ⟨9729052302491492747470573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12972069736655323663294097 9729052302491492747470573)
              ·
                refine ⟨3648394613434309780301465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9729052302491492747470573 3648394613434309780301465)
                ·
                  refine ⟨2736295960075732335226099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3648394613434309780301465 2736295960075732335226099)
                  ·
                    refine ⟨4104443940113598502839149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736295960075732335226099 4104443940113598502839149)
                    ·
                      refine ⟨1539166477542599438564681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104443940113598502839149 1539166477542599438564681)
                      ·
                        rfl

theorem cell23_2997516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_2997516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997516 prefixEnd_2997516 := by exact prefixLift 2997516
  have htrace : WordTrace (prefixWord ++ tailWord_2997516) baseStart_2997516 baseEnd_2997516 := by
    simpa [prefixWord, tailWord_2997516, baseEnd_2997516] using wordTrace_append hprefix tailTrace_2997516
  have hstable : (prefixWord ++ tailWord_2997516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997516).length < 2 ^ (prefixWord ++ tailWord_2997516).sum := by decide
  have hdescent : baseEnd_2997516 < baseStart_2997516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997534 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2997534 : Nat := 118140960795 + 2997534 * 2 ^ 59
def prefixEnd_2997534 : Nat := 4983230072969 + 3 ^ 40 * 2997534 * 2
def baseEnd_2997534 : Nat := 1539175720194380368139599

theorem tailTrace_2997534 : CollatzResearch.WordTrace tailWord_2997534 prefixEnd_2997534 1539175720194380368139599 := by
  unfold tailWord_2997534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666130840306716361854957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72886031148302487263226437 13666130840306716361854957)
  ·
    refine ⟨5124799065115018635695609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13666130840306716361854957 5124799065115018635695609)
    ·
      refine ⟨3843599298836263976771707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5124799065115018635695609 3843599298836263976771707)
      ·
        refine ⟨5765398948254395965157561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843599298836263976771707 5765398948254395965157561)
        ·
          refine ⟨4324049211190796973868171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765398948254395965157561 4324049211190796973868171)
          ·
            refine ⟨6486073816786195460802257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324049211190796973868171 6486073816786195460802257)
            ·
              refine ⟨4864555362589646595601693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6486073816786195460802257 4864555362589646595601693)
              ·
                refine ⟨1824208260971117473350635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4864555362589646595601693 1824208260971117473350635)
                ·
                  refine ⟨2736312391456676210025953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824208260971117473350635 2736312391456676210025953)
                  ·
                    refine ⟨2052234293592507157519465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2736312391456676210025953 2052234293592507157519465)
                    ·
                      refine ⟨1539175720194380368139599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052234293592507157519465 1539175720194380368139599)
                      ·
                        rfl

theorem cell23_2997534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2997534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997534 prefixEnd_2997534 := by exact prefixLift 2997534
  have htrace : WordTrace (prefixWord ++ tailWord_2997534) baseStart_2997534 baseEnd_2997534 := by
    simpa [prefixWord, tailWord_2997534, baseEnd_2997534] using wordTrace_append hprefix tailTrace_2997534
  have hstable : (prefixWord ++ tailWord_2997534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997534).length < 2 ^ (prefixWord ++ tailWord_2997534).sum := by decide
  have hdescent : baseEnd_2997534 < baseStart_2997534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997552 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_2997552 : Nat := 118140960795 + 2997552 * 2 ^ 59
def prefixEnd_2997552 : Nat := 4983230072969 + 3 ^ 40 * 2997552 * 2
def baseEnd_2997552 : Nat := 1539184962846161297714515

theorem tailTrace_2997552 : CollatzResearch.WordTrace tailWord_2997552 prefixEnd_2997552 1539184962846161297714515 := by
  unfold tailWord_2997552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54664851618194259984497455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72886468824259013312663273 54664851618194259984497455)
  ·
    refine ⟨81997277427291389976746183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54664851618194259984497455 81997277427291389976746183)
    ·
      refine ⟨122995916140937084965119275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81997277427291389976746183 122995916140937084965119275)
      ·
        refine ⟨184493874211405627447678913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122995916140937084965119275 184493874211405627447678913)
        ·
          refine ⟨138370405658554220585759185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184493874211405627447678913 138370405658554220585759185)
          ·
            refine ⟨103777804243915665439319389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138370405658554220585759185 103777804243915665439319389)
            ·
              refine ⟨38916676591468374539744771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103777804243915665439319389 38916676591468374539744771)
              ·
                refine ⟨58375014887202561809617157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38916676591468374539744771 58375014887202561809617157)
                ·
                  refine ⟨10945315291350480339303217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58375014887202561809617157 10945315291350480339303217)
                  ·
                    refine ⟨8208986468512860254477413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10945315291350480339303217 8208986468512860254477413)
                    ·
                      refine ⟨1539184962846161297714515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8208986468512860254477413 1539184962846161297714515)
                      ·
                        rfl

theorem cell23_2997552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_2997552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997552 prefixEnd_2997552 := by exact prefixLift 2997552
  have htrace : WordTrace (prefixWord ++ tailWord_2997552) baseStart_2997552 baseEnd_2997552 := by
    simpa [prefixWord, tailWord_2997552, baseEnd_2997552] using wordTrace_append hprefix tailTrace_2997552
  have hstable : (prefixWord ++ tailWord_2997552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997552).length < 2 ^ (prefixWord ++ tailWord_2997552).sum := by decide
  have hdescent : baseEnd_2997552 < baseStart_2997552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997592 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_2997592 : Nat := 118140960795 + 2997592 * 2 ^ 59
def prefixEnd_2997592 : Nat := 4983230072969 + 3 ^ 40 * 2997592 * 2
def baseEnd_2997592 : Nat := 513068500690780380404777

theorem tailTrace_2997592 : CollatzResearch.WordTrace tailWord_2997592 prefixEnd_2997592 513068500690780380404777 := by
  unfold tailWord_2997592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54665581078121803400225515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72887441437495737866967353 54665581078121803400225515)
  ·
    refine ⟨81998371617182705100338273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54665581078121803400225515 81998371617182705100338273)
    ·
      refine ⟨61498778712887028825253705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81998371617182705100338273 61498778712887028825253705)
      ·
        refine ⟨46124084034665271618940279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61498778712887028825253705 46124084034665271618940279)
        ·
          refine ⟨69186126051997907428410419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46124084034665271618940279 69186126051997907428410419)
          ·
            refine ⟨103779189077996861142615629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69186126051997907428410419 103779189077996861142615629)
            ·
              refine ⟨38917195904248822928480861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103779189077996861142615629 38917195904248822928480861)
              ·
                refine ⟨14593948464093308598180323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38917195904248822928480861 14593948464093308598180323)
                ·
                  refine ⟨21890922696139962897270485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14593948464093308598180323 21890922696139962897270485)
                  ·
                    refine ⟨513068500690780380404777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21890922696139962897270485 513068500690780380404777)
                    ·
                      rfl

theorem cell23_2997592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_2997592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997592 prefixEnd_2997592 := by exact prefixLift 2997592
  have htrace : WordTrace (prefixWord ++ tailWord_2997592) baseStart_2997592 baseEnd_2997592 := by
    simpa [prefixWord, tailWord_2997592, baseEnd_2997592] using wordTrace_append hprefix tailTrace_2997592
  have hstable : (prefixWord ++ tailWord_2997592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997592).length < 2 ^ (prefixWord ++ tailWord_2997592).sum := by decide
  have hdescent : baseEnd_2997592 < baseStart_2997592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997599 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 7, 2]
def baseStart_2997599 : Nat := 118140960795 + 2997599 * 2 ^ 59
def prefixEnd_2997599 : Nat := 4983230072969 + 3 ^ 40 * 2997599 * 2
def baseEnd_2997599 : Nat := 1539209096436922613826799

theorem tailTrace_2997599 : CollatzResearch.WordTrace tailWord_2997599 prefixEnd_2997599 1539209096436922613826799 := by
  unfold tailWord_2997599
  simp only [CollatzResearch.WordTrace]
  refine ⟨109331417467218246995955851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72887611644812164663970567 109331417467218246995955851)
  ·
    refine ⟨163997126200827370493933777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109331417467218246995955851 163997126200827370493933777)
    ·
      refine ⟨122997844650620527870450333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163997126200827370493933777 122997844650620527870450333)
      ·
        refine ⟨46124191743982697951418875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122997844650620527870450333 46124191743982697951418875)
        ·
          refine ⟨69186287615974046927128313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46124191743982697951418875 69186287615974046927128313)
          ·
            refine ⟨51889715711980535195346235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69186287615974046927128313 51889715711980535195346235)
            ·
              refine ⟨77834573567970802793019353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51889715711980535195346235 77834573567970802793019353)
              ·
                refine ⟨58375930175978102094764515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77834573567970802793019353 58375930175978102094764515)
                ·
                  refine ⟨87563895263967153142146773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58375930175978102094764515 87563895263967153142146773)
                  ·
                    refine ⟨2052278795249230151769065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 87563895263967153142146773 2052278795249230151769065)
                    ·
                      refine ⟨1539209096436922613826799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052278795249230151769065 1539209096436922613826799)
                      ·
                        rfl

theorem cell23_2997599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_2997599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997599 prefixEnd_2997599 := by exact prefixLift 2997599
  have htrace : WordTrace (prefixWord ++ tailWord_2997599) baseStart_2997599 baseEnd_2997599 := by
    simpa [prefixWord, tailWord_2997599, baseEnd_2997599] using wordTrace_append hprefix tailTrace_2997599
  have hstable : (prefixWord ++ tailWord_2997599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997599).length < 2 ^ (prefixWord ++ tailWord_2997599).sum := by decide
  have hdescent : baseEnd_2997599 < baseStart_2997599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997613 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 5]
def baseStart_2997613 : Nat := 118140960795 + 2997613 * 2 ^ 59
def prefixEnd_2997613 : Nat := 4983230072969 + 3 ^ 40 * 2997613 * 2
def baseEnd_2997613 : Nat := 171024031685120617672415

theorem tailTrace_2997613 : CollatzResearch.WordTrace tailWord_2997613 prefixEnd_2997613 171024031685120617672415 := by
  unfold tailWord_2997613
  simp only [CollatzResearch.WordTrace]
  refine ⟨109331928089167527386965493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72887952059445018257976995 109331928089167527386965493)
  ·
    refine ⟨10249868258359455692528015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109331928089167527386965493 10249868258359455692528015)
    ·
      refine ⟨15374802387539183538792023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10249868258359455692528015 15374802387539183538792023)
      ·
        refine ⟨23062203581308775308188035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15374802387539183538792023 23062203581308775308188035)
        ·
          refine ⟨34593305371963162962282053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23062203581308775308188035 34593305371963162962282053)
          ·
            refine ⟨6486244757243093055427885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34593305371963162962282053 6486244757243093055427885)
            ·
              refine ⟨2432341783966159895785457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6486244757243093055427885 2432341783966159895785457)
              ·
                refine ⟨1824256337974619921839093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2432341783966159895785457 1824256337974619921839093)
                ·
                  refine ⟨171024031685120617672415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824256337974619921839093 171024031685120617672415)
                  ·
                    rfl

theorem cell23_2997613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_2997613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997613 prefixEnd_2997613 := by exact prefixLift 2997613
  have htrace : WordTrace (prefixWord ++ tailWord_2997613) baseStart_2997613 baseEnd_2997613 := by
    simpa [prefixWord, tailWord_2997613, baseEnd_2997613] using wordTrace_append hprefix tailTrace_2997613
  have hstable : (prefixWord ++ tailWord_2997613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997613).length < 2 ^ (prefixWord ++ tailWord_2997613).sum := by decide
  have hdescent : baseEnd_2997613 < baseStart_2997613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997629 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_2997629 : Nat := 118140960795 + 2997629 * 2 ^ 59
def prefixEnd_2997629 : Nat := 4983230072969 + 3 ^ 40 * 2997629 * 2
def baseEnd_2997629 : Nat := 1539224500856557496451661

theorem tailTrace_2997629 : CollatzResearch.WordTrace tailWord_2997629 prefixEnd_2997629 1539224500856557496451661 := by
  unfold tailWord_2997629
  simp only [CollatzResearch.WordTrace]
  refine ⟨109332511657109562119547941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72888341104739708079698627 109332511657109562119547941)
  ·
    refine ⟨20499845935708042897415239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109332511657109562119547941 20499845935708042897415239)
    ·
      refine ⟨30749768903562064346122859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20499845935708042897415239 30749768903562064346122859)
      ·
        refine ⟨46124653355343096519184289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30749768903562064346122859 46124653355343096519184289)
        ·
          refine ⟨34593490016507322389388217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46124653355343096519184289 34593490016507322389388217)
          ·
            refine ⟨25945117512380491792041163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34593490016507322389388217 25945117512380491792041163)
            ·
              refine ⟨38917676268570737688061745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25945117512380491792041163 38917676268570737688061745)
              ·
                refine ⟨29188257201428053266046309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38917676268570737688061745 29188257201428053266046309)
                ·
                  refine ⟨5472798225267759987383683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29188257201428053266046309 5472798225267759987383683)
                  ·
                    refine ⟨8209197337901639981075525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5472798225267759987383683 8209197337901639981075525)
                    ·
                      refine ⟨1539224500856557496451661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8209197337901639981075525 1539224500856557496451661)
                      ·
                        rfl

theorem cell23_2997629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_2997629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997629 prefixEnd_2997629 := by exact prefixLift 2997629
  have htrace : WordTrace (prefixWord ++ tailWord_2997629) baseStart_2997629 baseEnd_2997629 := by
    simpa [prefixWord, tailWord_2997629, baseEnd_2997629] using wordTrace_append hprefix tailTrace_2997629
  have hstable : (prefixWord ++ tailWord_2997629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997629).length < 2 ^ (prefixWord ++ tailWord_2997629).sum := by decide
  have hdescent : baseEnd_2997629 < baseStart_2997629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997632 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_2997632 : Nat := 118140960795 + 2997632 * 2 ^ 59
def prefixEnd_2997632 : Nat := 4983230072969 + 3 ^ 40 * 2997632 * 2
def baseEnd_2997632 : Nat := 1539226041298520984714147

theorem tailTrace_2997632 : CollatzResearch.WordTrace tailWord_2997632 prefixEnd_2997632 1539226041298520984714147 := by
  unfold tailWord_2997632
  simp only [CollatzResearch.WordTrace]
  refine ⟨54666310538049346815953575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72888414050732462421271433 54666310538049346815953575)
  ·
    refine ⟨81999465807074020223930363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54666310538049346815953575 81999465807074020223930363)
    ·
      refine ⟨122999198710611030335895545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81999465807074020223930363 122999198710611030335895545)
      ·
        refine ⟨92249399032958272751921659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122999198710611030335895545 92249399032958272751921659)
        ·
          refine ⟨138374098549437409127882489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92249399032958272751921659 138374098549437409127882489)
          ·
            refine ⟨103780573912078056845911867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138374098549437409127882489 103780573912078056845911867)
            ·
              refine ⟨155670860868117085268867801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103780573912078056845911867 155670860868117085268867801)
              ·
                refine ⟨116753145651087813951650851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155670860868117085268867801 116753145651087813951650851)
                ·
                  refine ⟨175129718476631720927476277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116753145651087813951650851 175129718476631720927476277)
                  ·
                    refine ⟨16418411107184223836950901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175129718476631720927476277 16418411107184223836950901)
                    ·
                      refine ⟨1539226041298520984714147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16418411107184223836950901 1539226041298520984714147)
                      ·
                        rfl

theorem cell23_2997632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_2997632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997632 prefixEnd_2997632 := by exact prefixLift 2997632
  have htrace : WordTrace (prefixWord ++ tailWord_2997632) baseStart_2997632 baseEnd_2997632 := by
    simpa [prefixWord, tailWord_2997632, baseEnd_2997632] using wordTrace_append hprefix tailTrace_2997632
  have hstable : (prefixWord ++ tailWord_2997632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997632).length < 2 ^ (prefixWord ++ tailWord_2997632).sum := by decide
  have hdescent : baseEnd_2997632 < baseStart_2997632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997649 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_2997649 : Nat := 118140960795 + 2997649 * 2 ^ 59
def prefixEnd_2997649 : Nat := 4983230072969 + 3 ^ 40 * 2997649 * 2
def baseEnd_2997649 : Nat := 1539234770469647418201569

theorem tailTrace_2997649 : CollatzResearch.WordTrace tailWord_2997649 prefixEnd_2997649 1539234770469647418201569 := by
  unfold tailWord_2997649
  simp only [CollatzResearch.WordTrace]
  refine ⟨109333241117037105535276001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72888827411358070356850667 109333241117037105535276001)
  ·
    refine ⟨81999930837777829151457001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109333241117037105535276001 81999930837777829151457001)
    ·
      refine ⟨61499948128333371863592751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81999930837777829151457001 61499948128333371863592751)
      ·
        refine ⟨92249922192500057795389127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61499948128333371863592751 92249922192500057795389127)
        ·
          refine ⟨138374883288750086693083691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92249922192500057795389127 138374883288750086693083691)
          ·
            refine ⟨207562324933125130039625537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138374883288750086693083691 207562324933125130039625537)
            ·
              refine ⟨155671743699843847529719153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207562324933125130039625537 155671743699843847529719153)
              ·
                refine ⟨116753807774882885647289365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155671743699843847529719153 116753807774882885647289365)
                ·
                  refine ⟨5472834739447635264716689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116753807774882885647289365 5472834739447635264716689)
                  ·
                    refine ⟨4104626054585726448537517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5472834739447635264716689 4104626054585726448537517)
                    ·
                      refine ⟨1539234770469647418201569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104626054585726448537517 1539234770469647418201569)
                      ·
                        rfl

theorem cell23_2997649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_2997649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997649 prefixEnd_2997649 := by exact prefixLift 2997649
  have htrace : WordTrace (prefixWord ++ tailWord_2997649) baseStart_2997649 baseEnd_2997649 := by
    simpa [prefixWord, tailWord_2997649, baseEnd_2997649] using wordTrace_append hprefix tailTrace_2997649
  have hstable : (prefixWord ++ tailWord_2997649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997649).length < 2 ^ (prefixWord ++ tailWord_2997649).sum := by decide
  have hdescent : baseEnd_2997649 < baseStart_2997649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997696 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 5, 1, 3]
def baseStart_2997696 : Nat := 118140960795 + 2997696 * 2 ^ 59
def prefixEnd_2997696 : Nat := 4983230072969 + 3 ^ 40 * 2997696 * 2
def baseEnd_2997696 : Nat := 1539258904060408734313853

theorem tailTrace_2997696 : CollatzResearch.WordTrace tailWord_2997696 prefixEnd_2997696 1539258904060408734313853 := by
  unfold tailWord_2997696
  simp only [CollatzResearch.WordTrace]
  refine ⟨54667477673933416281118471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72889970231911221708157961 54667477673933416281118471)
  ·
    refine ⟨82001216510900124421677707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54667477673933416281118471 82001216510900124421677707)
    ·
      refine ⟨123001824766350186632516561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82001216510900124421677707 123001824766350186632516561)
      ·
        refine ⟨92251368574762639974387421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123001824766350186632516561 92251368574762639974387421)
        ·
          refine ⟨34594263215535989990395283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92251368574762639974387421 34594263215535989990395283)
          ·
            refine ⟨51891394823303984985592925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34594263215535989990395283 51891394823303984985592925)
            ·
              refine ⟨19459273058738994369597347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51891394823303984985592925 19459273058738994369597347)
              ·
                refine ⟨29188909588108491554396021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19459273058738994369597347 29188909588108491554396021)
                ·
                  refine ⟨2736460273885171083224627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29188909588108491554396021 2736460273885171083224627)
                  ·
                    refine ⟨4104690410827756624836941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736460273885171083224627 4104690410827756624836941)
                    ·
                      refine ⟨1539258904060408734313853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104690410827756624836941 1539258904060408734313853)
                      ·
                        rfl

theorem cell23_2997696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_2997696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997696 prefixEnd_2997696 := by exact prefixLift 2997696
  have htrace : WordTrace (prefixWord ++ tailWord_2997696) baseStart_2997696 baseEnd_2997696 := by
    simpa [prefixWord, tailWord_2997696, baseEnd_2997696] using wordTrace_append hprefix tailTrace_2997696
  have hstable : (prefixWord ++ tailWord_2997696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997696).length < 2 ^ (prefixWord ++ tailWord_2997696).sum := by decide
  have hdescent : baseEnd_2997696 < baseStart_2997696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997699 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 3, 5]
def baseStart_2997699 : Nat := 118140960795 + 2997699 * 2 ^ 59
def prefixEnd_2997699 : Nat := 4983230072969 + 3 ^ 40 * 2997699 * 2
def baseEnd_2997699 : Nat := 513086814834124074192113

theorem tailTrace_2997699 : CollatzResearch.WordTrace tailWord_2997699 prefixEnd_2997699 513086814834124074192113 := by
  unfold tailWord_2997699
  simp only [CollatzResearch.WordTrace]
  refine ⟨109335064766855964074596151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72890043177903976049730767 109335064766855964074596151)
  ·
    refine ⟨164002597150283946111894227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109335064766855964074596151 164002597150283946111894227)
    ·
      refine ⟨246003895725425919167841341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164002597150283946111894227 246003895725425919167841341)
      ·
        refine ⟨92251460897034719687940503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246003895725425919167841341 92251460897034719687940503)
        ·
          refine ⟨138377191345552079531910755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92251460897034719687940503 138377191345552079531910755)
          ·
            refine ⟨207565787018328119297866133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138377191345552079531910755 207565787018328119297866133)
            ·
              refine ⟨9729646266484130592087475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207565787018328119297866133 9729646266484130592087475)
              ·
                refine ⟨14594469399726195888131213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729646266484130592087475 14594469399726195888131213)
                ·
                  refine ⟨5472926024897323458049205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14594469399726195888131213 5472926024897323458049205)
                  ·
                    refine ⟨513086814834124074192113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5472926024897323458049205 513086814834124074192113)
                    ·
                      rfl

theorem cell23_2997699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 5].length) (baseStart_2997699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997699 prefixEnd_2997699 := by exact prefixLift 2997699
  have htrace : WordTrace (prefixWord ++ tailWord_2997699) baseStart_2997699 baseEnd_2997699 := by
    simpa [prefixWord, tailWord_2997699, baseEnd_2997699] using wordTrace_append hprefix tailTrace_2997699
  have hstable : (prefixWord ++ tailWord_2997699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997699).length < 2 ^ (prefixWord ++ tailWord_2997699).sum := by decide
  have hdescent : baseEnd_2997699 < baseStart_2997699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997700 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2997700 : Nat := 118140960795 + 2997700 * 2 ^ 59
def prefixEnd_2997700 : Nat := 4983230072969 + 3 ^ 40 * 2997700 * 2
def baseEnd_2997700 : Nat := 1539260957983026718663835

theorem tailTrace_2997700 : CollatzResearch.WordTrace tailWord_2997700 prefixEnd_2997700 1539260957983026718663835 := by
  unfold tailWord_2997700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54667550619926170622691277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72890067493234894163588369 54667550619926170622691277)
  ·
    refine ⟨20500331482472313983509229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54667550619926170622691277 20500331482472313983509229)
    ·
      refine ⟨7687624305927117743815961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20500331482472313983509229 7687624305927117743815961)
      ·
        refine ⟨5765718229445338307861971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7687624305927117743815961 5765718229445338307861971)
        ·
          refine ⟨8648577344168007461792957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765718229445338307861971 8648577344168007461792957)
          ·
            refine ⟨3243216504063002798172359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8648577344168007461792957 3243216504063002798172359)
            ·
              refine ⟨4864824756094504197258539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243216504063002798172359 4864824756094504197258539)
              ·
                refine ⟨7297237134141756295887809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864824756094504197258539 7297237134141756295887809)
                ·
                  refine ⟨5472927850606317221915857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297237134141756295887809 5472927850606317221915857)
                  ·
                    refine ⟨4104695887954737916436893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5472927850606317221915857 4104695887954737916436893)
                    ·
                      refine ⟨1539260957983026718663835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104695887954737916436893 1539260957983026718663835)
                      ·
                        rfl

theorem cell23_2997700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2997700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997700 prefixEnd_2997700 := by exact prefixLift 2997700
  have htrace : WordTrace (prefixWord ++ tailWord_2997700) baseStart_2997700 baseEnd_2997700 := by
    simpa [prefixWord, tailWord_2997700, baseEnd_2997700] using wordTrace_append hprefix tailTrace_2997700
  have hstable : (prefixWord ++ tailWord_2997700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997700).length < 2 ^ (prefixWord ++ tailWord_2997700).sum := by decide
  have hdescent : baseEnd_2997700 < baseStart_2997700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997739 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 3]
def baseStart_2997739 : Nat := 118140960795 + 2997739 * 2 ^ 59
def prefixEnd_2997739 : Nat := 4983230072969 + 3 ^ 40 * 2997739 * 2
def baseEnd_2997739 : Nat := 1539280983728552066076155

theorem tailTrace_2997739 : CollatzResearch.WordTrace tailWord_2997739 prefixEnd_2997739 1539280983728552066076155 := by
  unfold tailWord_2997739
  simp only [CollatzResearch.WordTrace]
  refine ⟨109336523686711050906052271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72891015791140700604034847 109336523686711050906052271)
  ·
    refine ⟨164004785530066576359078407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109336523686711050906052271 164004785530066576359078407)
    ·
      refine ⟨246007178295099864538617611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164004785530066576359078407 246007178295099864538617611)
      ·
        refine ⟨369010767442649796807926417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246007178295099864538617611 369010767442649796807926417)
        ·
          refine ⟨276758075581987347605944813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369010767442649796807926417 276758075581987347605944813)
          ·
            refine ⟨103784278343245255352229305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276758075581987347605944813 103784278343245255352229305)
            ·
              refine ⟨77838208757433941514171979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103784278343245255352229305 77838208757433941514171979)
              ·
                refine ⟨116757313136150912271257969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77838208757433941514171979 116757313136150912271257969)
                ·
                  refine ⟨87567984852113184203443477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116757313136150912271257969 87567984852113184203443477)
                  ·
                    refine ⟨4104749289942805509536413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87567984852113184203443477 4104749289942805509536413)
                    ·
                      refine ⟨1539280983728552066076155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104749289942805509536413 1539280983728552066076155)
                      ·
                        rfl

theorem cell23_2997739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 3].length) (baseStart_2997739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997739 prefixEnd_2997739 := by exact prefixLift 2997739
  have htrace : WordTrace (prefixWord ++ tailWord_2997739) baseStart_2997739 baseEnd_2997739 := by
    simpa [prefixWord, tailWord_2997739, baseEnd_2997739] using wordTrace_append hprefix tailTrace_2997739
  have hstable : (prefixWord ++ tailWord_2997739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997739).length < 2 ^ (prefixWord ++ tailWord_2997739).sum := by decide
  have hdescent : baseEnd_2997739 < baseStart_2997739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997756 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_2997756 : Nat := 118140960795 + 2997756 * 2 ^ 59
def prefixEnd_2997756 : Nat := 4983230072969 + 3 ^ 40 * 2997756 * 2
def baseEnd_2997756 : Nat := 1539289712899678499563577

theorem tailTrace_2997756 : CollatzResearch.WordTrace tailWord_2997756 prefixEnd_2997756 1539289712899678499563577 := by
  unfold tailWord_2997756
  simp only [CollatzResearch.WordTrace]
  refine ⟨54668571863824731404710561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72891429151766308539614081 54668571863824731404710561)
  ·
    refine ⟨41001428897868548553532921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54668571863824731404710561 41001428897868548553532921)
    ·
      refine ⟨30751071673401411415149691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41001428897868548553532921 30751071673401411415149691)
      ·
        refine ⟨46126607510102117122724537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30751071673401411415149691 46126607510102117122724537)
        ·
          refine ⟨34594955632576587842043403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46126607510102117122724537 34594955632576587842043403)
          ·
            refine ⟨51892433448864881763065105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34594955632576587842043403 51892433448864881763065105)
            ·
              refine ⟨38919325086648661322298829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51892433448864881763065105 38919325086648661322298829)
              ·
                refine ⟨14594746907493247995862061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38919325086648661322298829 14594746907493247995862061)
                ·
                  refine ⟨5473030090309967998448273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14594746907493247995862061 5473030090309967998448273)
                  ·
                    refine ⟨4104772567732475998836205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473030090309967998448273 4104772567732475998836205)
                    ·
                      refine ⟨1539289712899678499563577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104772567732475998836205 1539289712899678499563577)
                      ·
                        rfl

theorem cell23_2997756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_2997756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997756 prefixEnd_2997756 := by exact prefixLift 2997756
  have htrace : WordTrace (prefixWord ++ tailWord_2997756) baseStart_2997756 baseEnd_2997756 := by
    simpa [prefixWord, tailWord_2997756, baseEnd_2997756] using wordTrace_append hprefix tailTrace_2997756
  have hstable : (prefixWord ++ tailWord_2997756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997756).length < 2 ^ (prefixWord ++ tailWord_2997756).sum := by decide
  have hdescent : baseEnd_2997756 < baseStart_2997756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997764 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2997764 : Nat := 118140960795 + 2997764 * 2 ^ 59
def prefixEnd_2997764 : Nat := 4983230072969 + 3 ^ 40 * 2997764 * 2
def baseEnd_2997764 : Nat := 1539293820744914468263541

theorem tailTrace_2997764 : CollatzResearch.WordTrace tailWord_2997764 prefixEnd_2997764 1539293820744914468263541 := by
  unfold tailWord_2997764
  simp only [CollatzResearch.WordTrace]
  refine ⟨54668717755810240087856173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72891623674413653450474897 54668717755810240087856173)
  ·
    refine ⟨20500769158428840032946065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54668717755810240087856173 20500769158428840032946065)
    ·
      refine ⟨15375576868821630024709549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20500769158428840032946065 15375576868821630024709549)
      ·
        refine ⟨5765841325808111259266081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15375576868821630024709549 5765841325808111259266081)
        ·
          refine ⟨4324380994356083444449561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765841325808111259266081 4324380994356083444449561)
          ·
            refine ⟨3243285745767062583337171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324380994356083444449561 3243285745767062583337171)
            ·
              refine ⟨4864928618650593875005757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243285745767062583337171 4864928618650593875005757)
              ·
                refine ⟨1824348231993972703127159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4864928618650593875005757 1824348231993972703127159)
                ·
                  refine ⟨2736522347990959054690739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824348231993972703127159 2736522347990959054690739)
                  ·
                    refine ⟨4104783521986438582036109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736522347990959054690739 4104783521986438582036109)
                    ·
                      refine ⟨1539293820744914468263541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4104783521986438582036109 1539293820744914468263541)
                      ·
                        rfl

theorem cell23_2997764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2997764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997764 prefixEnd_2997764 := by exact prefixLift 2997764
  have htrace : WordTrace (prefixWord ++ tailWord_2997764) baseStart_2997764 baseEnd_2997764 := by
    simpa [prefixWord, tailWord_2997764, baseEnd_2997764] using wordTrace_append hprefix tailTrace_2997764
  have hstable : (prefixWord ++ tailWord_2997764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997764).length < 2 ^ (prefixWord ++ tailWord_2997764).sum := by decide
  have hdescent : baseEnd_2997764 < baseStart_2997764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997809 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2997809 : Nat := 118140960795 + 2997809 * 2 ^ 59
def prefixEnd_2997809 : Nat := 4983230072969 + 3 ^ 40 * 2997809 * 2
def baseEnd_2997809 : Nat := 1539316927374366792200833

theorem tailTrace_2997809 : CollatzResearch.WordTrace tailWord_2997809 prefixEnd_2997809 1539316927374366792200833 := by
  unfold tailWord_2997809
  simp only [CollatzResearch.WordTrace]
  refine ⟨109339076796457452861100481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72892717864304968574066987 109339076796457452861100481)
  ·
    refine ⟨82004307597343089645825361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109339076796457452861100481 82004307597343089645825361)
    ·
      refine ⟨61503230698007317234369021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82004307597343089645825361 61503230698007317234369021)
      ·
        refine ⟨23063711511752743962888383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61503230698007317234369021 23063711511752743962888383)
        ·
          refine ⟨34595567267629115944332575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23063711511752743962888383 34595567267629115944332575)
          ·
            refine ⟨51893350901443673916498863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34595567267629115944332575 51893350901443673916498863)
            ·
              refine ⟨77840026352165510874748295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51893350901443673916498863 77840026352165510874748295)
              ·
                refine ⟨116760039528248266312122443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77840026352165510874748295 116760039528248266312122443)
                ·
                  refine ⟨175140059292372399468183665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116760039528248266312122443 175140059292372399468183665)
                  ·
                    refine ⟨131355044469279299601137749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175140059292372399468183665 131355044469279299601137749)
                    ·
                      refine ⟨1539316927374366792200833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 131355044469279299601137749 1539316927374366792200833)
                      ·
                        rfl

theorem cell23_2997809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2997809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997809 prefixEnd_2997809 := by exact prefixLift 2997809
  have htrace : WordTrace (prefixWord ++ tailWord_2997809) baseStart_2997809 baseEnd_2997809 := by
    simpa [prefixWord, tailWord_2997809, baseEnd_2997809] using wordTrace_append hprefix tailTrace_2997809
  have hstable : (prefixWord ++ tailWord_2997809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997809).length < 2 ^ (prefixWord ++ tailWord_2997809).sum := by decide
  have hdescent : baseEnd_2997809 < baseStart_2997809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997839 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_2997839 : Nat := 118140960795 + 2997839 * 2 ^ 59
def prefixEnd_2997839 : Nat := 4983230072969 + 3 ^ 40 * 2997839 * 2
def baseEnd_2997839 : Nat := 1539332331794001674825695

theorem tailTrace_2997839 : CollatzResearch.WordTrace tailWord_2997839 prefixEnd_2997839 1539332331794001674825695 := by
  unfold tailWord_2997839
  simp only [CollatzResearch.WordTrace]
  refine ⟨109340170986348767984692571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72893447324232511989795047 109340170986348767984692571)
  ·
    refine ⟨164010256479523151977038857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109340170986348767984692571 164010256479523151977038857)
    ·
      refine ⟨123007692359642363982779143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164010256479523151977038857 123007692359642363982779143)
      ·
        refine ⟨184511538539463545974168715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123007692359642363982779143 184511538539463545974168715)
        ·
          refine ⟨276767307809195318961253073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184511538539463545974168715 276767307809195318961253073)
          ·
            refine ⟨207575480856896489220939805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276767307809195318961253073 207575480856896489220939805)
            ·
              refine ⟨77840805321336183457852427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207575480856896489220939805 77840805321336183457852427)
              ·
                refine ⟨116761207982004275186778641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77840805321336183457852427 116761207982004275186778641)
                ·
                  refine ⟨87570905986503206390083981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116761207982004275186778641 87570905986503206390083981)
                  ·
                    refine ⟨32839089744938702396281493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87570905986503206390083981 32839089744938702396281493)
                    ·
                      refine ⟨1539332331794001674825695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32839089744938702396281493 1539332331794001674825695)
                      ·
                        rfl

theorem cell23_2997839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_2997839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997839 prefixEnd_2997839 := by exact prefixLift 2997839
  have htrace : WordTrace (prefixWord ++ tailWord_2997839) baseStart_2997839 baseEnd_2997839 := by
    simpa [prefixWord, tailWord_2997839, baseEnd_2997839] using wordTrace_append hprefix tailTrace_2997839
  have hstable : (prefixWord ++ tailWord_2997839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997839).length < 2 ^ (prefixWord ++ tailWord_2997839).sum := by decide
  have hdescent : baseEnd_2997839 < baseStart_2997839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997849 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 11]
def baseStart_2997849 : Nat := 118140960795 + 2997849 * 2 ^ 59
def prefixEnd_2997849 : Nat := 4983230072969 + 3 ^ 40 * 2997849 * 2
def baseEnd_2997849 : Nat := 171037496288949626188961

theorem tailTrace_2997849 : CollatzResearch.WordTrace tailWord_2997849 prefixEnd_2997849 171037496288949626188961 := by
  unfold tailWord_2997849
  simp only [CollatzResearch.WordTrace]
  refine ⟨109340535716312539692556601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72893690477541693128371067 109340535716312539692556601)
  ·
    refine ⟨82005401787234404769417451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109340535716312539692556601 82005401787234404769417451)
    ·
      refine ⟨123008102680851607154126177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82005401787234404769417451 123008102680851607154126177)
      ·
        refine ⟨92256077010638705365594633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123008102680851607154126177 92256077010638705365594633)
        ·
          refine ⟨69192057757979029024195975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92256077010638705365594633 69192057757979029024195975)
          ·
            refine ⟨103788086636968543536293963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69192057757979029024195975 103788086636968543536293963)
            ·
              refine ⟨155682129955452815304440945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103788086636968543536293963 155682129955452815304440945)
              ·
                refine ⟨116761597466589611478330709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155682129955452815304440945 116761597466589611478330709)
                ·
                  refine ⟨171037496288949626188961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 116761597466589611478330709 171037496288949626188961)
                  ·
                    rfl

theorem cell23_2997849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_2997849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997849 prefixEnd_2997849 := by exact prefixLift 2997849
  have htrace : WordTrace (prefixWord ++ tailWord_2997849) baseStart_2997849 baseEnd_2997849 := by
    simpa [prefixWord, tailWord_2997849, baseEnd_2997849] using wordTrace_append hprefix tailTrace_2997849
  have hstable : (prefixWord ++ tailWord_2997849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997849).length < 2 ^ (prefixWord ++ tailWord_2997849).sum := by decide
  have hdescent : baseEnd_2997849 < baseStart_2997849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997860 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_2997860 : Nat := 118140960795 + 2997860 * 2 ^ 59
def prefixEnd_2997860 : Nat := 4983230072969 + 3 ^ 40 * 2997860 * 2
def baseEnd_2997860 : Nat := 1539343114887746092663099

theorem tailTrace_2997860 : CollatzResearch.WordTrace tailWord_2997860 prefixEnd_2997860 1539343114887746092663099 := by
  unfold tailWord_2997860
  simp only [CollatzResearch.WordTrace]
  refine ⟨54670468459636344285603517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72893957946181792380804689 54670468459636344285603517)
  ·
    refine ⟨20501425672363629107101319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54670468459636344285603517 20501425672363629107101319)
    ·
      refine ⟨30752138508545443660651979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20501425672363629107101319 30752138508545443660651979)
      ·
        refine ⟨46128207762818165490977969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30752138508545443660651979 46128207762818165490977969)
        ·
          refine ⟨34596155822113624118233477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46128207762818165490977969 34596155822113624118233477)
          ·
            refine ⟨6486779216646304522168777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34596155822113624118233477 6486779216646304522168777)
            ·
              refine ⟨4865084412484728391626583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6486779216646304522168777 4865084412484728391626583)
              ·
                refine ⟨7297626618727092587439875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865084412484728391626583 7297626618727092587439875)
                ·
                  refine ⟨10946439928090638881159813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297626618727092587439875 10946439928090638881159813)
                  ·
                    refine ⟨2052457486516994790217465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10946439928090638881159813 2052457486516994790217465)
                    ·
                      refine ⟨1539343114887746092663099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052457486516994790217465 1539343114887746092663099)
                      ·
                        rfl

theorem cell23_2997860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_2997860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997860 prefixEnd_2997860 := by exact prefixLift 2997860
  have htrace : WordTrace (prefixWord ++ tailWord_2997860) baseStart_2997860 baseEnd_2997860 := by
    simpa [prefixWord, tailWord_2997860, baseEnd_2997860] using wordTrace_append hprefix tailTrace_2997860
  have hstable : (prefixWord ++ tailWord_2997860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997860).length < 2 ^ (prefixWord ++ tailWord_2997860).sum := by decide
  have hdescent : baseEnd_2997860 < baseStart_2997860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997866 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_2997866 : Nat := 118140960795 + 2997866 * 2 ^ 59
def prefixEnd_2997866 : Nat := 4983230072969 + 3 ^ 40 * 2997866 * 2
def baseEnd_2997866 : Nat := 171038466196852563243119

theorem tailTrace_2997866 : CollatzResearch.WordTrace tailWord_2997866 prefixEnd_2997866 171038466196852563243119 := by
  unfold tailWord_2997866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27335288939312737898981363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72894103838167301063950301 27335288939312737898981363)
  ·
    refine ⟨41002933408969106848472045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27335288939312737898981363 41002933408969106848472045)
    ·
      refine ⟨15376100028363415068177017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41002933408969106848472045 15376100028363415068177017)
      ·
        refine ⟨11532075021272561301132763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15376100028363415068177017 11532075021272561301132763)
        ·
          refine ⟨17298112531908841951699145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532075021272561301132763 17298112531908841951699145)
          ·
            refine ⟨12973584398931631463774359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17298112531908841951699145 12973584398931631463774359)
            ·
              refine ⟨19460376598397447195661539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12973584398931631463774359 19460376598397447195661539)
              ·
                refine ⟨29190564897596170793492309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19460376598397447195661539 29190564897596170793492309)
                ·
                  refine ⟨171038466196852563243119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29190564897596170793492309 171038466196852563243119)
                  ·
                    rfl

theorem cell23_2997866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_2997866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997866 prefixEnd_2997866 := by exact prefixLift 2997866
  have htrace : WordTrace (prefixWord ++ tailWord_2997866) baseStart_2997866 baseEnd_2997866 := by
    simpa [prefixWord, tailWord_2997866, baseEnd_2997866] using wordTrace_append hprefix tailTrace_2997866
  have hstable : (prefixWord ++ tailWord_2997866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997866).length < 2 ^ (prefixWord ++ tailWord_2997866).sum := by decide
  have hdescent : baseEnd_2997866 < baseStart_2997866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997883 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 5]
def baseStart_2997883 : Nat := 118140960795 + 2997883 * 2 ^ 59
def prefixEnd_2997883 : Nat := 4983230072969 + 3 ^ 40 * 2997883 * 2
def baseEnd_2997883 : Nat := 171039436104755500297277

theorem tailTrace_2997883 : CollatzResearch.WordTrace tailWord_2997883 prefixEnd_2997883 171039436104755500297277 := by
  unfold tailWord_2997883
  simp only [CollatzResearch.WordTrace]
  refine ⟨109341775798189363499294303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72894517198792908999529535 109341775798189363499294303)
  ·
    refine ⟨164012663697284045248941455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109341775798189363499294303 164012663697284045248941455)
    ·
      refine ⟨246018995545926067873412183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164012663697284045248941455 246018995545926067873412183)
      ·
        refine ⟨369028493318889101810118275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246018995545926067873412183 369028493318889101810118275)
        ·
          refine ⟨553542739978333652715177413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369028493318889101810118275 553542739978333652715177413)
          ·
            refine ⟨103789263745937559884095765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 553542739978333652715177413 103789263745937559884095765)
            ·
              refine ⟨4865121738090823119566989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103789263745937559884095765 4865121738090823119566989)
              ·
                refine ⟨1824420651784058669837621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4865121738090823119566989 1824420651784058669837621)
                ·
                  refine ⟨171039436104755500297277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824420651784058669837621 171039436104755500297277)
                  ·
                    rfl

theorem cell23_2997883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 5].length) (baseStart_2997883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997883 prefixEnd_2997883 := by exact prefixLift 2997883
  have htrace : WordTrace (prefixWord ++ tailWord_2997883) baseStart_2997883 baseEnd_2997883 := by
    simpa [prefixWord, tailWord_2997883, baseEnd_2997883] using wordTrace_append hprefix tailTrace_2997883
  have hstable : (prefixWord ++ tailWord_2997883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997883).length < 2 ^ (prefixWord ++ tailWord_2997883).sum := by decide
  have hdescent : baseEnd_2997883 < baseStart_2997883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997933 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2997933 : Nat := 118140960795 + 2997933 * 2 ^ 59
def prefixEnd_2997933 : Nat := 4983230072969 + 3 ^ 40 * 2997933 * 2
def baseEnd_2997933 : Nat := 1539380598975524307050263

theorem tailTrace_2997933 : CollatzResearch.WordTrace tailWord_2997933 prefixEnd_2997933 1539380598975524307050263 := by
  unfold tailWord_2997933
  simp only [CollatzResearch.WordTrace]
  refine ⟨109343599448008222038614453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72895732965338814692409635 109343599448008222038614453)
  ·
    refine ⟨10250962448250770816120105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109343599448008222038614453 10250962448250770816120105)
    ·
      refine ⟨7688221836188078112090079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10250962448250770816120105 7688221836188078112090079)
      ·
        refine ⟨11532332754282117168135119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688221836188078112090079 11532332754282117168135119)
        ·
          refine ⟨17298499131423175752202679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532332754282117168135119 17298499131423175752202679)
          ·
            refine ⟨25947748697134763628304019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17298499131423175752202679 25947748697134763628304019)
            ·
              refine ⟨38921623045702145442456029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25947748697134763628304019 38921623045702145442456029)
              ·
                refine ⟨14595608642138304540921011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38921623045702145442456029 14595608642138304540921011)
                ·
                  refine ⟨21893412963207456811381517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14595608642138304540921011 21893412963207456811381517)
                  ·
                    refine ⟨8210029861202796304268069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21893412963207456811381517 8210029861202796304268069)
                    ·
                      refine ⟨1539380598975524307050263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8210029861202796304268069 1539380598975524307050263)
                      ·
                        rfl

theorem cell23_2997933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2997933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997933 prefixEnd_2997933 := by exact prefixLift 2997933
  have htrace : WordTrace (prefixWord ++ tailWord_2997933) baseStart_2997933 baseEnd_2997933 := by
    simpa [prefixWord, tailWord_2997933, baseEnd_2997933] using wordTrace_append hprefix tailTrace_2997933
  have hstable : (prefixWord ++ tailWord_2997933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997933).length < 2 ^ (prefixWord ++ tailWord_2997933).sum := by decide
  have hdescent : baseEnd_2997933 < baseStart_2997933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997934 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_2997934 : Nat := 118140960795 + 2997934 * 2 ^ 59
def prefixEnd_2997934 : Nat := 4983230072969 + 3 ^ 40 * 2997934 * 2
def baseEnd_2997934 : Nat := 171042345828464311459751

theorem tailTrace_2997934 : CollatzResearch.WordTrace tailWord_2997934 prefixEnd_2997934 171042345828464311459751 := by
  unfold tailWord_2997934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13667954490125574901175107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72895757280669732806267237 13667954490125574901175107)
  ·
    refine ⟨20501931735188362351762661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13667954490125574901175107 20501931735188362351762661)
    ·
      refine ⟨3844112200347817940955499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20501931735188362351762661 3844112200347817940955499)
      ·
        refine ⟨5766168300521726911433249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844112200347817940955499 5766168300521726911433249)
        ·
          refine ⟨4324626225391295183574937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5766168300521726911433249 4324626225391295183574937)
          ·
            refine ⟨3243469669043471387681203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324626225391295183574937 3243469669043471387681203)
            ·
              refine ⟨4865204503565207081521805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243469669043471387681203 4865204503565207081521805)
              ·
                refine ⟨1824451688836952655570677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4865204503565207081521805 1824451688836952655570677)
                ·
                  refine ⟨171042345828464311459751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824451688836952655570677 171042345828464311459751)
                  ·
                    rfl

theorem cell23_2997934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_2997934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997934 prefixEnd_2997934 := by exact prefixLift 2997934
  have htrace : WordTrace (prefixWord ++ tailWord_2997934) baseStart_2997934 baseEnd_2997934 := by
    simpa [prefixWord, tailWord_2997934, baseEnd_2997934] using wordTrace_append hprefix tailTrace_2997934
  have hstable : (prefixWord ++ tailWord_2997934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997934).length < 2 ^ (prefixWord ++ tailWord_2997934).sum := by decide
  have hdescent : baseEnd_2997934 < baseStart_2997934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997950 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2997950 : Nat := 118140960795 + 2997950 * 2 ^ 59
def prefixEnd_2997950 : Nat := 4983230072969 + 3 ^ 40 * 2997950 * 2
def baseEnd_2997950 : Nat := 1539389328146650740537685

theorem tailTrace_2997950 : CollatzResearch.WordTrace tailWord_2997950 prefixEnd_2997950 1539389328146650740537685 := by
  unfold tailWord_2997950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13668027436118329242747913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72896146325964422627988869 13668027436118329242747913)
  ·
    refine ⟨10251020577088746932060935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13668027436118329242747913 10251020577088746932060935)
    ·
      refine ⟨15376530865633120398091403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10251020577088746932060935 15376530865633120398091403)
      ·
        refine ⟨23064796298449680597137105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15376530865633120398091403 23064796298449680597137105)
        ·
          refine ⟨17298597223837260447852829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23064796298449680597137105 17298597223837260447852829)
          ·
            refine ⟨6486973958938972667944811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17298597223837260447852829 6486973958938972667944811)
            ·
              refine ⟨9730460938408459001917217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486973958938972667944811 9730460938408459001917217)
              ·
                refine ⟨7297845703806344251437913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9730460938408459001917217 7297845703806344251437913)
                ·
                  refine ⟨5473384277854758188578435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297845703806344251437913 5473384277854758188578435)
                  ·
                    refine ⟨8210076416782137282867653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5473384277854758188578435 8210076416782137282867653)
                    ·
                      refine ⟨1539389328146650740537685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8210076416782137282867653 1539389328146650740537685)
                      ·
                        rfl

theorem cell23_2997950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2997950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997950 prefixEnd_2997950 := by exact prefixLift 2997950
  have htrace : WordTrace (prefixWord ++ tailWord_2997950) baseStart_2997950 baseEnd_2997950 := by
    simpa [prefixWord, tailWord_2997950, baseEnd_2997950] using wordTrace_append hprefix tailTrace_2997950
  have hstable : (prefixWord ++ tailWord_2997950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997950).length < 2 ^ (prefixWord ++ tailWord_2997950).sum := by decide
  have hdescent : baseEnd_2997950 < baseStart_2997950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997987 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2997987 : Nat := 118140960795 + 2997987 * 2 ^ 59
def prefixEnd_2997987 : Nat := 4983230072969 + 3 ^ 40 * 2997987 * 2
def baseEnd_2997987 : Nat := 1539408326930867095775015

theorem tailTrace_2997987 : CollatzResearch.WordTrace tailWord_2997987 prefixEnd_2997987 1539408326930867095775015 := by
  unfold tailWord_2997987
  simp only [CollatzResearch.WordTrace]
  refine ⟨109345568989812589261080215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72897045993208392840720143 109345568989812589261080215)
  ·
    refine ⟨164018353484718883891620323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109345568989812589261080215 164018353484718883891620323)
    ·
      refine ⟨246027530227078325837430485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164018353484718883891620323 246027530227078325837430485)
      ·
        refine ⟨5766270239697148261814777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 246027530227078325837430485 5766270239697148261814777)
        ·
          refine ⟨4324702679772861196361083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5766270239697148261814777 4324702679772861196361083)
          ·
            refine ⟨6487054019659291794541625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324702679772861196361083 6487054019659291794541625)
            ·
              refine ⟨4865290514744468845906219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487054019659291794541625 4865290514744468845906219)
              ·
                refine ⟨7297935772116703268859329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865290514744468845906219 7297935772116703268859329)
                ·
                  refine ⟨5473451829087527451644497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297935772116703268859329 5473451829087527451644497)
                  ·
                    refine ⟨4105088871815645588733373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473451829087527451644497 4105088871815645588733373)
                    ·
                      refine ⟨1539408326930867095775015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105088871815645588733373 1539408326930867095775015)
                      ·
                        rfl

theorem cell23_2997987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2997987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2997987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2997987 prefixEnd_2997987 := by exact prefixLift 2997987
  have htrace : WordTrace (prefixWord ++ tailWord_2997987) baseStart_2997987 baseEnd_2997987 := by
    simpa [prefixWord, tailWord_2997987, baseEnd_2997987] using wordTrace_append hprefix tailTrace_2997987
  have hstable : (prefixWord ++ tailWord_2997987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997987).length < 2 ^ (prefixWord ++ tailWord_2997987).sum := by decide
  have hdescent : baseEnd_2997987 < baseStart_2997987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998003 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 1, 5]
def baseStart_2998003 : Nat := 118140960795 + 2998003 * 2 ^ 59
def prefixEnd_2998003 : Nat := 4983230072969 + 3 ^ 40 * 2998003 * 2
def baseEnd_2998003 : Nat := 513138847540446344391647

theorem tailTrace_2998003 : CollatzResearch.WordTrace tailWord_2998003 prefixEnd_2998003 513138847540446344391647 := by
  unfold tailWord_2998003
  simp only [CollatzResearch.WordTrace]
  refine ⟨109346152557754623993662663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72897435038503082662441775 109346152557754623993662663)
  ·
    refine ⟨164019228836631935990493995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109346152557754623993662663 164019228836631935990493995)
    ·
      refine ⟨246028843254947903985740993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164019228836631935990493995 246028843254947903985740993)
      ·
        refine ⟨184521632441210927989305745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246028843254947903985740993 184521632441210927989305745)
        ·
          refine ⟨138391224330908195991979309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184521632441210927989305745 138391224330908195991979309)
          ·
            refine ⟨51896709124090573496992241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138391224330908195991979309 51896709124090573496992241)
            ·
              refine ⟨38922531843067930122744181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51896709124090573496992241 38922531843067930122744181)
              ·
                refine ⟨3648987360287618449007267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38922531843067930122744181 3648987360287618449007267)
                ·
                  refine ⟨5473481040431427673510901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648987360287618449007267 5473481040431427673510901)
                  ·
                    refine ⟨513138847540446344391647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5473481040431427673510901 513138847540446344391647)
                    ·
                      rfl

theorem cell23_2998003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 5].length) (baseStart_2998003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998003 prefixEnd_2998003 := by exact prefixLift 2998003
  have htrace : WordTrace (prefixWord ++ tailWord_2998003) baseStart_2998003 baseEnd_2998003 := by
    simpa [prefixWord, tailWord_2998003, baseEnd_2998003] using wordTrace_append hprefix tailTrace_2998003
  have hstable : (prefixWord ++ tailWord_2998003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998003).length < 2 ^ (prefixWord ++ tailWord_2998003).sum := by decide
  have hdescent : baseEnd_2998003 < baseStart_2998003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998004 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2998004 : Nat := 118140960795 + 2998004 * 2 ^ 59
def prefixEnd_2998004 : Nat := 4983230072969 + 3 ^ 40 * 2998004 * 2
def baseEnd_2998004 : Nat := 1539417056101993529262437

theorem tailTrace_2998004 : CollatzResearch.WordTrace tailWord_2998004 prefixEnd_2998004 1539417056101993529262437 := by
  unfold tailWord_2998004
  simp only [CollatzResearch.WordTrace]
  refine ⟨54673094515375500582224533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72897459353834000776299377 54673094515375500582224533)
  ·
    refine ⟨2562801305408226589791775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54673094515375500582224533 2562801305408226589791775)
    ·
      refine ⟨3844201958112339884687663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562801305408226589791775 3844201958112339884687663)
      ·
        refine ⟨5766302937168509827031495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844201958112339884687663 5766302937168509827031495)
        ·
          refine ⟨8649454405752764740547243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5766302937168509827031495 8649454405752764740547243)
          ·
            refine ⟨12974181608629147110820865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8649454405752764740547243 12974181608629147110820865)
            ·
              refine ⟨9730636206471860333115649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12974181608629147110820865 9730636206471860333115649)
              ·
                refine ⟨7297977154853895249836737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9730636206471860333115649 7297977154853895249836737)
                ·
                  refine ⟨5473482866140421437377553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297977154853895249836737 5473482866140421437377553)
                  ·
                    refine ⟨4105112149605316078033165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473482866140421437377553 4105112149605316078033165)
                    ·
                      refine ⟨1539417056101993529262437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105112149605316078033165 1539417056101993529262437)
                      ·
                        rfl

theorem cell23_2998004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2998004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998004 prefixEnd_2998004 := by exact prefixLift 2998004
  have htrace : WordTrace (prefixWord ++ tailWord_2998004) baseStart_2998004 baseEnd_2998004 := by
    simpa [prefixWord, tailWord_2998004, baseEnd_2998004] using wordTrace_append hprefix tailTrace_2998004
  have hstable : (prefixWord ++ tailWord_2998004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998004).length < 2 ^ (prefixWord ++ tailWord_2998004).sum := by decide
  have hdescent : baseEnd_2998004 < baseStart_2998004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998033 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 6, 4]
def baseStart_2998033 : Nat := 118140960795 + 2998033 * 2 ^ 59
def prefixEnd_2998033 : Nat := 4983230072969 + 3 ^ 40 * 2998033 * 2
def baseEnd_2998033 : Nat := 513143982346991305266601

theorem tailTrace_2998033 : CollatzResearch.WordTrace tailWord_2998033 prefixEnd_2998033 513143982346991305266601 := by
  unfold tailWord_2998033
  simp only [CollatzResearch.WordTrace]
  refine ⟨109347246747645939117254753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72898164498430626078169835 109347246747645939117254753)
  ·
    refine ⟨82010435060734454337941065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109347246747645939117254753 82010435060734454337941065)
    ·
      refine ⟨61507826295550840753455799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82010435060734454337941065 61507826295550840753455799)
      ·
        refine ⟨92261739443326261130183699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61507826295550840753455799 92261739443326261130183699)
        ·
          refine ⟨138392609164989391695275549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92261739443326261130183699 138392609164989391695275549)
          ·
            refine ⟨51897228436871021885728331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138392609164989391695275549 51897228436871021885728331)
            ·
              refine ⟨77845842655306532828592497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51897228436871021885728331 77845842655306532828592497)
              ·
                refine ⟨58384381991479899621444373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77845842655306532828592497 58384381991479899621444373)
                ·
                  refine ⟨2736767905850620294755205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58384381991479899621444373 2736767905850620294755205)
                  ·
                    refine ⟨513143982346991305266601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2736767905850620294755205 513143982346991305266601)
                    ·
                      rfl

theorem cell23_2998033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_2998033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998033 prefixEnd_2998033 := by exact prefixLift 2998033
  have htrace : WordTrace (prefixWord ++ tailWord_2998033) baseStart_2998033 baseEnd_2998033 := by
    simpa [prefixWord, tailWord_2998033, baseEnd_2998033] using wordTrace_append hprefix tailTrace_2998033
  have hstable : (prefixWord ++ tailWord_2998033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998033).length < 2 ^ (prefixWord ++ tailWord_2998033).sum := by decide
  have hdescent : baseEnd_2998033 < baseStart_2998033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998034 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2998034 : Nat := 118140960795 + 2998034 * 2 ^ 59
def prefixEnd_2998034 : Nat := 4983230072969 + 3 ^ 40 * 2998034 * 2
def baseEnd_2998034 : Nat := 1539432460521628411887299

theorem tailTrace_2998034 : CollatzResearch.WordTrace tailWord_2998034 prefixEnd_2998034 1539432460521628411887299 := by
  unfold tailWord_2998034
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336820805160579072010289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72898188813761544192027437 27336820805160579072010289)
  ·
    refine ⟨20502615603870434304007717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27336820805160579072010289 20502615603870434304007717)
    ·
      refine ⟨3844240425725706432001447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20502615603870434304007717 3844240425725706432001447)
      ·
        refine ⟨5766360638588559648002171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844240425725706432001447 5766360638588559648002171)
        ·
          refine ⟨8649540957882839472003257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5766360638588559648002171 8649540957882839472003257)
          ·
            refine ⟨6487155718412129604002443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8649540957882839472003257 6487155718412129604002443)
            ·
              refine ⟨9730733577618194406003665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487155718412129604002443 9730733577618194406003665)
              ·
                refine ⟨7298050183213645804502749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9730733577618194406003665 7298050183213645804502749)
                ·
                  refine ⟨2736768818705117176688531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7298050183213645804502749 2736768818705117176688531)
                  ·
                    refine ⟨4105153228057675765032797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736768818705117176688531 4105153228057675765032797)
                    ·
                      refine ⟨1539432460521628411887299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105153228057675765032797 1539432460521628411887299)
                      ·
                        rfl

theorem cell23_2998034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2998034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998034 prefixEnd_2998034 := by exact prefixLift 2998034
  have htrace : WordTrace (prefixWord ++ tailWord_2998034) baseStart_2998034 baseEnd_2998034 := by
    simpa [prefixWord, tailWord_2998034, baseEnd_2998034] using wordTrace_append hprefix tailTrace_2998034
  have hstable : (prefixWord ++ tailWord_2998034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998034).length < 2 ^ (prefixWord ++ tailWord_2998034).sum := by decide
  have hdescent : baseEnd_2998034 < baseStart_2998034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998050 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2998050 : Nat := 118140960795 + 2998050 * 2 ^ 59
def prefixEnd_2998050 : Nat := 4983230072969 + 3 ^ 40 * 2998050 * 2
def baseEnd_2998050 : Nat := 513146892070700116429075

theorem tailTrace_2998050 : CollatzResearch.WordTrace tailWord_2998050 prefixEnd_2998050 513146892070700116429075 := by
  unfold tailWord_2998050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336966697146087755155901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72898577859056234013749069 27336966697146087755155901)
  ·
    refine ⟨10251362511429782908183463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27336966697146087755155901 10251362511429782908183463)
    ·
      refine ⟨15377043767144674362275195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10251362511429782908183463 15377043767144674362275195)
      ·
        refine ⟨23065565650717011543412793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15377043767144674362275195 23065565650717011543412793)
        ·
          refine ⟨17299174238037758657559595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23065565650717011543412793 17299174238037758657559595)
          ·
            refine ⟨25948761357056637986339393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17299174238037758657559595 25948761357056637986339393)
            ·
              refine ⟨19461571017792478489754545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25948761357056637986339393 19461571017792478489754545)
              ·
                refine ⟨14596178263344358867315909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19461571017792478489754545 14596178263344358867315909)
                ·
                  refine ⟨2736783424377067287621733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14596178263344358867315909 2736783424377067287621733)
                  ·
                    refine ⟨513146892070700116429075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2736783424377067287621733 513146892070700116429075)
                    ·
                      rfl

theorem cell23_2998050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2998050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998050 prefixEnd_2998050 := by exact prefixLift 2998050
  have htrace : WordTrace (prefixWord ++ tailWord_2998050) baseStart_2998050 baseEnd_2998050 := by
    simpa [prefixWord, tailWord_2998050, baseEnd_2998050] using wordTrace_append hprefix tailTrace_2998050
  have hstable : (prefixWord ++ tailWord_2998050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998050).length < 2 ^ (prefixWord ++ tailWord_2998050).sum := by decide
  have hdescent : baseEnd_2998050 < baseStart_2998050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998074 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2]
def baseStart_2998074 : Nat := 118140960795 + 2998074 * 2 ^ 59
def prefixEnd_2998074 : Nat := 4983230072969 + 3 ^ 40 * 2998074 * 2
def baseEnd_2998074 : Nat := 1539452999747808255387115

theorem tailTrace_2998074 : CollatzResearch.WordTrace tailWord_2998074 prefixEnd_2998074 1539452999747808255387115 := by
  unfold tailWord_2998074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27337185535124350779874319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72899161426998268746331517 27337185535124350779874319)
  ·
    refine ⟨41005778302686526169811479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27337185535124350779874319 41005778302686526169811479)
    ·
      refine ⟨61508667454029789254717219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41005778302686526169811479 61508667454029789254717219)
      ·
        refine ⟨92263001181044683882075829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61508667454029789254717219 92263001181044683882075829)
        ·
          refine ⟨8649656360722939113944609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92263001181044683882075829 8649656360722939113944609)
          ·
            refine ⟨6487242270542204335458457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8649656360722939113944609 6487242270542204335458457)
            ·
              refine ⟨4865431702906653251593843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487242270542204335458457 4865431702906653251593843)
              ·
                refine ⟨7298147554359979877390765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865431702906653251593843 7298147554359979877390765)
                ·
                  refine ⟨2736805332884992454021537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7298147554359979877390765 2736805332884992454021537)
                  ·
                    refine ⟨2052603999663744340516153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2736805332884992454021537 2052603999663744340516153)
                    ·
                      refine ⟨1539452999747808255387115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052603999663744340516153 1539452999747808255387115)
                      ·
                        rfl

theorem cell23_2998074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_2998074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998074 prefixEnd_2998074 := by exact prefixLift 2998074
  have htrace : WordTrace (prefixWord ++ tailWord_2998074) baseStart_2998074 baseEnd_2998074 := by
    simpa [prefixWord, tailWord_2998074, baseEnd_2998074] using wordTrace_append hprefix tailTrace_2998074
  have hstable : (prefixWord ++ tailWord_2998074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998074).length < 2 ^ (prefixWord ++ tailWord_2998074).sum := by decide
  have hdescent : baseEnd_2998074 < baseStart_2998074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998143 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_2998143 : Nat := 118140960795 + 2998143 * 2 ^ 59
def prefixEnd_2998143 : Nat := 4983230072969 + 3 ^ 40 * 2998143 * 2
def baseEnd_2998143 : Nat := 1539488429912968485424297

theorem tailTrace_2998143 : CollatzResearch.WordTrace tailWord_2998143 prefixEnd_2998143 1539488429912968485424297 := by
  unfold tailWord_2998143
  simp only [CollatzResearch.WordTrace]
  refine ⟨109351258777247427903759083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72900839184831618602506055 109351258777247427903759083)
  ·
    refine ⟨164026888165871141855638625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109351258777247427903759083 164026888165871141855638625)
    ·
      refine ⟨123020166124403356391728969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164026888165871141855638625 123020166124403356391728969)
      ·
        refine ⟨92265124593302517293796727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123020166124403356391728969 92265124593302517293796727)
        ·
          refine ⟨138397686889953775940695091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92265124593302517293796727 138397686889953775940695091)
          ·
            refine ⟨207596530334930663911042637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138397686889953775940695091 207596530334930663911042637)
            ·
              refine ⟨77848698875598998966640989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207596530334930663911042637 77848698875598998966640989)
              ·
                refine ⟨29193262078349624612490371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77848698875598998966640989 29193262078349624612490371)
                ·
                  refine ⟨43789893117524436918735557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29193262078349624612490371 43789893117524436918735557)
                  ·
                    refine ⟨8210604959535831922262917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43789893117524436918735557 8210604959535831922262917)
                    ·
                      refine ⟨1539488429912968485424297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8210604959535831922262917 1539488429912968485424297)
                      ·
                        rfl

theorem cell23_2998143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_2998143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998143 prefixEnd_2998143 := by exact prefixLift 2998143
  have htrace : WordTrace (prefixWord ++ tailWord_2998143) baseStart_2998143 baseEnd_2998143 := by
    simpa [prefixWord, tailWord_2998143, baseEnd_2998143] using wordTrace_append hprefix tailTrace_2998143
  have hstable : (prefixWord ++ tailWord_2998143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998143).length < 2 ^ (prefixWord ++ tailWord_2998143).sum := by decide
  have hdescent : baseEnd_2998143 < baseStart_2998143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998151 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_2998151 : Nat := 118140960795 + 2998151 * 2 ^ 59
def prefixEnd_2998151 : Nat := 4983230072969 + 3 ^ 40 * 2998151 * 2
def baseEnd_2998151 : Nat := 1539492537758204454124261

theorem tailTrace_2998151 : CollatzResearch.WordTrace tailWord_2998151 prefixEnd_2998151 1539492537758204454124261 := by
  unfold tailWord_2998151
  simp only [CollatzResearch.WordTrace]
  refine ⟨109351550561218445270050307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72901033707478963513366871 109351550561218445270050307)
  ·
    refine ⟨164027325841827667905075461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109351550561218445270050307 164027325841827667905075461)
    ·
      refine ⟨30755123595342687732201649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164027325841827667905075461 30755123595342687732201649)
      ·
        refine ⟨23066342696507015799151237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30755123595342687732201649 23066342696507015799151237)
        ·
          refine ⟨4324939255595065462340857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23066342696507015799151237 4324939255595065462340857)
          ·
            refine ⟨3243704441696299096755643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324939255595065462340857 3243704441696299096755643)
            ·
              refine ⟨4865556662544448645133465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243704441696299096755643 4865556662544448645133465)
              ·
                refine ⟨3649167496908336483850099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4865556662544448645133465 3649167496908336483850099)
                ·
                  refine ⟨5473751245362504725775149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649167496908336483850099 5473751245362504725775149)
                  ·
                    refine ⟨2052656717010939272165681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5473751245362504725775149 2052656717010939272165681)
                    ·
                      refine ⟨1539492537758204454124261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052656717010939272165681 1539492537758204454124261)
                      ·
                        rfl

theorem cell23_2998151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_2998151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998151 prefixEnd_2998151 := by exact prefixLift 2998151
  have htrace : WordTrace (prefixWord ++ tailWord_2998151) baseStart_2998151 baseEnd_2998151 := by
    simpa [prefixWord, tailWord_2998151, baseEnd_2998151] using wordTrace_append hprefix tailTrace_2998151
  have hstable : (prefixWord ++ tailWord_2998151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998151).length < 2 ^ (prefixWord ++ tailWord_2998151).sum := by decide
  have hdescent : baseEnd_2998151 < baseStart_2998151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998153 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 9]
def baseStart_2998153 : Nat := 118140960795 + 2998153 * 2 ^ 59
def prefixEnd_2998153 : Nat := 4983230072969 + 3 ^ 40 * 2998153 * 2
def baseEnd_2998153 : Nat := 171054840524390382922139

theorem tailTrace_2998153 : CollatzResearch.WordTrace tailWord_2998153 prefixEnd_2998153 171054840524390382922139 := by
  unfold tailWord_2998153
  simp only [CollatzResearch.WordTrace]
  refine ⟨109351623507211199611623113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72901082338140799741082075 109351623507211199611623113)
  ·
    refine ⟨82013717630408399708717335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109351623507211199611623113 82013717630408399708717335)
    ·
      refine ⟨123020576445612599563076003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82013717630408399708717335 123020576445612599563076003)
      ·
        refine ⟨184530864668418899344614005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123020576445612599563076003 184530864668418899344614005)
        ·
          refine ⟨17299768562664271813557563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184530864668418899344614005 17299768562664271813557563)
          ·
            refine ⟨25949652843996407720336345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17299768562664271813557563 25949652843996407720336345)
            ·
              refine ⟨19462239632997305790252259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25949652843996407720336345 19462239632997305790252259)
              ·
                refine ⟨29193359449495958685378389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19462239632997305790252259 29193359449495958685378389)
                ·
                  refine ⟨171054840524390382922139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29193359449495958685378389 171054840524390382922139)
                  ·
                    rfl

theorem cell23_2998153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_2998153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998153 prefixEnd_2998153 := by exact prefixLift 2998153
  have htrace : WordTrace (prefixWord ++ tailWord_2998153) baseStart_2998153 baseEnd_2998153 := by
    simpa [prefixWord, tailWord_2998153, baseEnd_2998153] using wordTrace_append hprefix tailTrace_2998153
  have hstable : (prefixWord ++ tailWord_2998153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998153).length < 2 ^ (prefixWord ++ tailWord_2998153).sum := by decide
  have hdescent : baseEnd_2998153 < baseStart_2998153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998164 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2998164 : Nat := 118140960795 + 2998164 * 2 ^ 59
def prefixEnd_2998164 : Nat := 4983230072969 + 3 ^ 40 * 2998164 * 2
def baseEnd_2998164 : Nat := 1539499213006712903261701

theorem tailTrace_2998164 : CollatzResearch.WordTrace tailWord_2998164 prefixEnd_2998164 1539499213006712903261701 := by
  unfold tailWord_2998164
  simp only [CollatzResearch.WordTrace]
  refine ⟨54676012355085674245136773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72901349806780898993515697 54676012355085674245136773)
  ·
    refine ⟨10251752316578563920963145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54676012355085674245136773 10251752316578563920963145)
    ·
      refine ⟨7688814237433922940722359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10251752316578563920963145 7688814237433922940722359)
      ·
        refine ⟨11533221356150884411083539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688814237433922940722359 11533221356150884411083539)
        ·
          refine ⟨17299832034226326616625309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533221356150884411083539 17299832034226326616625309)
          ·
            refine ⟨6487437012834872481234491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17299832034226326616625309 6487437012834872481234491)
            ·
              refine ⟨9731155519252308721851737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487437012834872481234491 9731155519252308721851737)
              ·
                refine ⟨7298366639439231541388803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9731155519252308721851737 7298366639439231541388803)
                ·
                  refine ⟨10947549959158847312083205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7298366639439231541388803 10947549959158847312083205)
                  ·
                    refine ⟨2052665617342283871015601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10947549959158847312083205 2052665617342283871015601)
                    ·
                      refine ⟨1539499213006712903261701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052665617342283871015601 1539499213006712903261701)
                      ·
                        rfl

theorem cell23_2998164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2998164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998164 prefixEnd_2998164 := by exact prefixLift 2998164
  have htrace : WordTrace (prefixWord ++ tailWord_2998164) baseStart_2998164 baseEnd_2998164 := by
    simpa [prefixWord, tailWord_2998164, baseEnd_2998164] using wordTrace_append hprefix tailTrace_2998164
  have hstable : (prefixWord ++ tailWord_2998164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998164).length < 2 ^ (prefixWord ++ tailWord_2998164).sum := by decide
  have hdescent : baseEnd_2998164 < baseStart_2998164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998168 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2998168 : Nat := 118140960795 + 2998168 * 2 ^ 59
def prefixEnd_2998168 : Nat := 4983230072969 + 3 ^ 40 * 2998168 * 2
def baseEnd_2998168 : Nat := 1539501266929330887611683

theorem tailTrace_2998168 : CollatzResearch.WordTrace tailWord_2998168 prefixEnd_2998168 1539501266929330887611683 := by
  unfold tailWord_2998168
  simp only [CollatzResearch.WordTrace]
  refine ⟨54676085301078428586709579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72901447068104571448946105 54676085301078428586709579)
  ·
    refine ⟨82014127951617642880064369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54676085301078428586709579 82014127951617642880064369)
    ·
      refine ⟨61510595963713232160048277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82014127951617642880064369 61510595963713232160048277)
      ·
        refine ⟨2883309185799057757502263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61510595963713232160048277 2883309185799057757502263)
        ·
          refine ⟨4324963778698586636253395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883309185799057757502263 4324963778698586636253395)
          ·
            refine ⟨6487445668047879954380093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324963778698586636253395 6487445668047879954380093)
            ·
              refine ⟨2432792125517954982892535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6487445668047879954380093 2432792125517954982892535)
              ·
                refine ⟨3649188188276932474338803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432792125517954982892535 3649188188276932474338803)
                ·
                  refine ⟨5473782282415398711508205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649188188276932474338803 5473782282415398711508205)
                  ·
                    refine ⟨2052668355905774516815577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5473782282415398711508205 2052668355905774516815577)
                    ·
                      refine ⟨1539501266929330887611683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052668355905774516815577 1539501266929330887611683)
                      ·
                        rfl

theorem cell23_2998168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2998168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998168 prefixEnd_2998168 := by exact prefixLift 2998168
  have htrace : WordTrace (prefixWord ++ tailWord_2998168) baseStart_2998168 baseEnd_2998168 := by
    simpa [prefixWord, tailWord_2998168, baseEnd_2998168] using wordTrace_append hprefix tailTrace_2998168
  have hstable : (prefixWord ++ tailWord_2998168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998168).length < 2 ^ (prefixWord ++ tailWord_2998168).sum := by decide
  have hdescent : baseEnd_2998168 < baseStart_2998168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998197 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2998197 : Nat := 118140960795 + 2998197 * 2 ^ 59
def prefixEnd_2998197 : Nat := 4983230072969 + 3 ^ 40 * 2998197 * 2
def baseEnd_2998197 : Nat := 1539516157868311274149049

theorem tailTrace_2998197 : CollatzResearch.WordTrace tailWord_2998197 prefixEnd_2998197 1539516157868311274149049 := by
  unfold tailWord_2998197
  simp only [CollatzResearch.WordTrace]
  refine ⟨109353228319051795126224845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72902152212701196750816563 109353228319051795126224845)
  ·
    refine ⟨41007460619644423172334317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109353228319051795126224845 41007460619644423172334317)
    ·
      refine ⟨15377797732366658689625369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41007460619644423172334317 15377797732366658689625369)
      ·
        refine ⟨11533348299274994017219027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15377797732366658689625369 11533348299274994017219027)
        ·
          refine ⟨17300022448912491025828541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533348299274994017219027 17300022448912491025828541)
          ·
            refine ⟨6487508418342184134685703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17300022448912491025828541 6487508418342184134685703)
            ·
              refine ⟨9731262627513276202028555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487508418342184134685703 9731262627513276202028555)
              ·
                refine ⟨14596893941269914303042833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9731262627513276202028555 14596893941269914303042833)
                ·
                  refine ⟨10947670455952435727282125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14596893941269914303042833 10947670455952435727282125)
                  ·
                    refine ⟨4105376420982163397730797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10947670455952435727282125 4105376420982163397730797)
                    ·
                      refine ⟨1539516157868311274149049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105376420982163397730797 1539516157868311274149049)
                      ·
                        rfl

theorem cell23_2998197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2998197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998197 prefixEnd_2998197 := by exact prefixLift 2998197
  have htrace : WordTrace (prefixWord ++ tailWord_2998197) baseStart_2998197 baseEnd_2998197 := by
    simpa [prefixWord, tailWord_2998197, baseEnd_2998197] using wordTrace_append hprefix tailTrace_2998197
  have hstable : (prefixWord ++ tailWord_2998197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998197).length < 2 ^ (prefixWord ++ tailWord_2998197).sum := by decide
  have hdescent : baseEnd_2998197 < baseStart_2998197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998213 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_2998213 : Nat := 118140960795 + 2998213 * 2 ^ 59
def prefixEnd_2998213 : Nat := 4983230072969 + 3 ^ 40 * 2998213 * 2
def baseEnd_2998213 : Nat := 513174791186261070516325

theorem tailTrace_2998213 : CollatzResearch.WordTrace tailWord_2998213 prefixEnd_2998213 513174791186261070516325 := by
  unfold tailWord_2998213
  simp only [CollatzResearch.WordTrace]
  refine ⟨109353811886993829858807293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72902541257995886572538195 109353811886993829858807293)
  ·
    refine ⟨41007679457622686197052735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109353811886993829858807293 41007679457622686197052735)
    ·
      refine ⟨61511519186434029295579103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41007679457622686197052735 61511519186434029295579103)
      ·
        refine ⟨92267278779651043943368655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61511519186434029295579103 92267278779651043943368655)
        ·
          refine ⟨138400918169476565915052983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92267278779651043943368655 138400918169476565915052983)
          ·
            refine ⟨207601377254214848872579475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138400918169476565915052983 207601377254214848872579475)
            ·
              refine ⟨311402065881322273308869213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207601377254214848872579475 311402065881322273308869213)
              ·
                refine ⟨116775774705495852490825955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311402065881322273308869213 116775774705495852490825955)
                ·
                  refine ⟨175163662058243778736238933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116775774705495852490825955 175163662058243778736238933)
                  ·
                    refine ⟨513174791186261070516325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 175163662058243778736238933 513174791186261070516325)
                    ·
                      rfl

theorem cell23_2998213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_2998213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998213 prefixEnd_2998213 := by exact prefixLift 2998213
  have htrace : WordTrace (prefixWord ++ tailWord_2998213) baseStart_2998213 baseEnd_2998213 := by
    simpa [prefixWord, tailWord_2998213, baseEnd_2998213] using wordTrace_append hprefix tailTrace_2998213
  have hstable : (prefixWord ++ tailWord_2998213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998213).length < 2 ^ (prefixWord ++ tailWord_2998213).sum := by decide
  have hdescent : baseEnd_2998213 < baseStart_2998213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998250 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2998250 : Nat := 118140960795 + 2998250 * 2 ^ 59
def prefixEnd_2998250 : Nat := 4983230072969 + 3 ^ 40 * 2998250 * 2
def baseEnd_2998250 : Nat := 1539543372342999566786305

theorem tailTrace_2998250 : CollatzResearch.WordTrace tailWord_2998250 prefixEnd_2998250 1539543372342999566786305 := by
  unfold tailWord_2998250
  simp only [CollatzResearch.WordTrace]
  refine ⟨27338790346964946294476051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72903440925239856785269469 27338790346964946294476051)
  ·
    refine ⟨41008185520447419441714077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27338790346964946294476051 41008185520447419441714077)
    ·
      refine ⟨15378069570167782290642779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41008185520447419441714077 15378069570167782290642779)
      ·
        refine ⟨23067104355251673435964169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15378069570167782290642779 23067104355251673435964169)
        ·
          refine ⟨17300328266438755076973127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23067104355251673435964169 17300328266438755076973127)
          ·
            refine ⟨25950492399658132615459691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17300328266438755076973127 25950492399658132615459691)
            ·
              refine ⟨38925738599487198923189537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25950492399658132615459691 38925738599487198923189537)
              ·
                refine ⟨29194303949615399192392153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38925738599487198923189537 29194303949615399192392153)
                ·
                  refine ⟨21895727962211549394294115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29194303949615399192392153 21895727962211549394294115)
                  ·
                    refine ⟨32843591943317324091441173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21895727962211549394294115 32843591943317324091441173)
                    ·
                      refine ⟨1539543372342999566786305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32843591943317324091441173 1539543372342999566786305)
                      ·
                        rfl

theorem cell23_2998250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2998250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998250 prefixEnd_2998250 := by exact prefixLift 2998250
  have htrace : WordTrace (prefixWord ++ tailWord_2998250) baseStart_2998250 baseEnd_2998250 := by
    simpa [prefixWord, tailWord_2998250, baseEnd_2998250] using wordTrace_append hprefix tailTrace_2998250
  have hstable : (prefixWord ++ tailWord_2998250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998250).length < 2 ^ (prefixWord ++ tailWord_2998250).sum := by decide
  have hdescent : baseEnd_2998250 < baseStart_2998250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998254 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_2998254 : Nat := 118140960795 + 2998254 * 2 ^ 59
def prefixEnd_2998254 : Nat := 4983230072969 + 3 ^ 40 * 2998254 * 2
def baseEnd_2998254 : Nat := 1539545426265617551136287

theorem tailTrace_2998254 : CollatzResearch.WordTrace tailWord_2998254 prefixEnd_2998254 1539545426265617551136287 := by
  unfold tailWord_2998254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669413409980661732631227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72903538186563529240699877 13669413409980661732631227)
  ·
    refine ⟨20504120114970992598946841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13669413409980661732631227 20504120114970992598946841)
    ·
      refine ⟨15378090086228244449210131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20504120114970992598946841 15378090086228244449210131)
      ·
        refine ⟨23067135129342366673815197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15378090086228244449210131 23067135129342366673815197)
        ·
          refine ⟨8650175673503387502680699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23067135129342366673815197 8650175673503387502680699)
          ·
            refine ⟨12975263510255081254021049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650175673503387502680699 12975263510255081254021049)
            ·
              refine ⟨9731447632691310940515787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12975263510255081254021049 9731447632691310940515787)
              ·
                refine ⟨14597171449036966410773681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9731447632691310940515787 14597171449036966410773681)
                ·
                  refine ⟨10947878586777724808080261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14597171449036966410773681 10947878586777724808080261)
                  ·
                    refine ⟨2052727235020823401515049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10947878586777724808080261 2052727235020823401515049)
                    ·
                      refine ⟨1539545426265617551136287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052727235020823401515049 1539545426265617551136287)
                      ·
                        rfl

theorem cell23_2998254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_2998254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998254 prefixEnd_2998254 := by exact prefixLift 2998254
  have htrace : WordTrace (prefixWord ++ tailWord_2998254) baseStart_2998254 baseEnd_2998254 := by
    simpa [prefixWord, tailWord_2998254, baseEnd_2998254] using wordTrace_append hprefix tailTrace_2998254
  have hstable : (prefixWord ++ tailWord_2998254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998254).length < 2 ^ (prefixWord ++ tailWord_2998254).sum := by decide
  have hdescent : baseEnd_2998254 < baseStart_2998254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998327 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 6, 2]
def baseStart_2998327 : Nat := 118140960795 + 2998327 * 2 ^ 59
def prefixEnd_2998327 : Nat := 4983230072969 + 3 ^ 40 * 2998327 * 2
def baseEnd_2998327 : Nat := 1539582910353395765523451

theorem tailTrace_2998327 : CollatzResearch.WordTrace tailWord_2998327 prefixEnd_2998327 1539582910353395765523451 := by
  unfold tailWord_2998327
  simp only [CollatzResearch.WordTrace]
  refine ⟨109357969808580827328457235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72905313205720551552304823 109357969808580827328457235)
  ·
    refine ⟨164036954712871240992685853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109357969808580827328457235 164036954712871240992685853)
    ·
      refine ⟨61513858017326715372257195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164036954712871240992685853 61513858017326715372257195)
      ·
        refine ⟨92270787025990073058385793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61513858017326715372257195 92270787025990073058385793)
        ·
          refine ⟨69203090269492554793789345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92270787025990073058385793 69203090269492554793789345)
          ·
            refine ⟨51902317702119416095342009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69203090269492554793789345 51902317702119416095342009)
            ·
              refine ⟨38926738276589562071506507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51902317702119416095342009 38926738276589562071506507)
              ·
                refine ⟨58390107414884343107259761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38926738276589562071506507 58390107414884343107259761)
                ·
                  refine ⟨43792580561163257330444821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58390107414884343107259761 43792580561163257330444821)
                  ·
                    refine ⟨2052777213804527687364601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43792580561163257330444821 2052777213804527687364601)
                    ·
                      refine ⟨1539582910353395765523451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052777213804527687364601 1539582910353395765523451)
                      ·
                        rfl

theorem cell23_2998327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_2998327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998327 prefixEnd_2998327 := by exact prefixLift 2998327
  have htrace : WordTrace (prefixWord ++ tailWord_2998327) baseStart_2998327 baseEnd_2998327 := by
    simpa [prefixWord, tailWord_2998327, baseEnd_2998327] using wordTrace_append hprefix tailTrace_2998327
  have hstable : (prefixWord ++ tailWord_2998327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998327).length < 2 ^ (prefixWord ++ tailWord_2998327).sum := by decide
  have hdescent : baseEnd_2998327 < baseStart_2998327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998337 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2998337 : Nat := 118140960795 + 2998337 * 2 ^ 59
def prefixEnd_2998337 : Nat := 4983230072969 + 3 ^ 40 * 2998337 * 2
def baseEnd_2998337 : Nat := 513196015053313575466135

theorem tailTrace_2998337 : CollatzResearch.WordTrace tailWord_2998337 prefixEnd_2998337 513196015053313575466135 := by
  unfold tailWord_2998337
  simp only [CollatzResearch.WordTrace]
  refine ⟨109358334538544599036321265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72905556359029732690880843 109358334538544599036321265)
  ·
    refine ⟨82018750903908449277240949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109358334538544599036321265 82018750903908449277240949)
    ·
      refine ⟨7689257897241417119741339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82018750903908449277240949 7689257897241417119741339)
      ·
        refine ⟨11533886845862125679612009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689257897241417119741339 11533886845862125679612009)
        ·
          refine ⟨8650415134396594259709007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11533886845862125679612009 8650415134396594259709007)
          ·
            refine ⟨12975622701594891389563511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650415134396594259709007 12975622701594891389563511)
            ·
              refine ⟨19463434052392337084345267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12975622701594891389563511 19463434052392337084345267)
              ·
                refine ⟨29195151078588505626517901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19463434052392337084345267 29195151078588505626517901)
                ·
                  refine ⟨10948181654470689609944213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29195151078588505626517901 10948181654470689609944213)
                  ·
                    refine ⟨513196015053313575466135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10948181654470689609944213 513196015053313575466135)
                    ·
                      rfl

theorem cell23_2998337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2998337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998337 prefixEnd_2998337 := by exact prefixLift 2998337
  have htrace : WordTrace (prefixWord ++ tailWord_2998337) baseStart_2998337 baseEnd_2998337 := by
    simpa [prefixWord, tailWord_2998337, baseEnd_2998337] using wordTrace_append hprefix tailTrace_2998337
  have hstable : (prefixWord ++ tailWord_2998337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998337).length < 2 ^ (prefixWord ++ tailWord_2998337).sum := by decide
  have hdescent : baseEnd_2998337 < baseStart_2998337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998344 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_2998344 : Nat := 118140960795 + 2998344 * 2 ^ 59
def prefixEnd_2998344 : Nat := 4983230072969 + 3 ^ 40 * 2998344 * 2
def baseEnd_2998344 : Nat := 1539591639524522199010873

theorem tailTrace_2998344 : CollatzResearch.WordTrace tailWord_2998344 prefixEnd_2998344 1539591639524522199010873 := by
  unfold tailWord_2998344
  simp only [CollatzResearch.WordTrace]
  refine ⟨54679294924759619615913043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72905726566346159487884057 54679294924759619615913043)
  ·
    refine ⟨82018942387139429423869565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54679294924759619615913043 82018942387139429423869565)
    ·
      refine ⟨30757103395177286033951087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82018942387139429423869565 30757103395177286033951087)
      ·
        refine ⟨46135655092765929050926631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30757103395177286033951087 46135655092765929050926631)
        ·
          refine ⟨69203482639148893576389947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46135655092765929050926631 69203482639148893576389947)
          ·
            refine ⟨103805223958723340364584921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69203482639148893576389947 103805223958723340364584921)
            ·
              refine ⟨77853917969042505273438691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103805223958723340364584921 77853917969042505273438691)
              ·
                refine ⟨116780876953563757910158037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77853917969042505273438691 116780876953563757910158037)
                ·
                  refine ⟨2737051803599150576019329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116780876953563757910158037 2737051803599150576019329)
                  ·
                    refine ⟨2052788852699362932014497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2737051803599150576019329 2052788852699362932014497)
                    ·
                      refine ⟨1539591639524522199010873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052788852699362932014497 1539591639524522199010873)
                      ·
                        rfl

theorem cell23_2998344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_2998344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998344 prefixEnd_2998344 := by exact prefixLift 2998344
  have htrace : WordTrace (prefixWord ++ tailWord_2998344) baseStart_2998344 baseEnd_2998344 := by
    simpa [prefixWord, tailWord_2998344, baseEnd_2998344] using wordTrace_append hprefix tailTrace_2998344
  have hstable : (prefixWord ++ tailWord_2998344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998344).length < 2 ^ (prefixWord ++ tailWord_2998344).sum := by decide
  have hdescent : baseEnd_2998344 < baseStart_2998344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998350 : List Nat := [4, 1, 1, 1, 1, 15]
def baseStart_2998350 : Nat := 118140960795 + 2998350 * 2 ^ 59
def prefixEnd_2998350 : Nat := 4983230072969 + 3 ^ 40 * 2998350 * 2
def baseEnd_2998350 : Nat := 6335780742421601545415

theorem tailTrace_2998350 : CollatzResearch.WordTrace tailWord_2998350 prefixEnd_2998350 6335780742421601545415 := by
  unfold tailWord_2998350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669851085937187782068063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72905872458331668171029669 13669851085937187782068063)
  ·
    refine ⟨20504776628905781673102095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13669851085937187782068063 20504776628905781673102095)
    ·
      refine ⟨30757164943358672509653143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20504776628905781673102095 30757164943358672509653143)
      ·
        refine ⟨46135747415038008764479715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30757164943358672509653143 46135747415038008764479715)
        ·
          refine ⟨69203621122557013146719573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46135747415038008764479715 69203621122557013146719573)
          ·
            refine ⟨6335780742421601545415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 69203621122557013146719573 6335780742421601545415)
            ·
              rfl

theorem cell23_2998350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 15].length) (baseStart_2998350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998350 prefixEnd_2998350 := by exact prefixLift 2998350
  have htrace : WordTrace (prefixWord ++ tailWord_2998350) baseStart_2998350 baseEnd_2998350 := by
    simpa [prefixWord, tailWord_2998350, baseEnd_2998350] using wordTrace_append hprefix tailTrace_2998350
  have hstable : (prefixWord ++ tailWord_2998350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998350).length < 2 ^ (prefixWord ++ tailWord_2998350).sum := by decide
  have hdescent : baseEnd_2998350 < baseStart_2998350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998364 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2998364 : Nat := 118140960795 + 2998364 * 2 ^ 59
def prefixEnd_2998364 : Nat := 4983230072969 + 3 ^ 40 * 2998364 * 2
def baseEnd_2998364 : Nat := 1539601909137612120760781

theorem tailTrace_2998364 : CollatzResearch.WordTrace tailWord_2998364 prefixEnd_2998364 1539601909137612120760781 := by
  unfold tailWord_2998364
  simp only [CollatzResearch.WordTrace]
  refine ⟨54679659654723391323777073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72906212872964521765036097 54679659654723391323777073)
  ·
    refine ⟨41009744741042543492832805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54679659654723391323777073 41009744741042543492832805)
    ·
      refine ⟨7689327138945476904906151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41009744741042543492832805 7689327138945476904906151)
      ·
        refine ⟨11533990708418215357359227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689327138945476904906151 11533990708418215357359227)
        ·
          refine ⟨17300986062627323036038841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533990708418215357359227 17300986062627323036038841)
          ·
            refine ⟨12975739546970492277029131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17300986062627323036038841 12975739546970492277029131)
            ·
              refine ⟨19463609320455738415543697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12975739546970492277029131 19463609320455738415543697)
              ·
                refine ⟨14597706990341803811657773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19463609320455738415543697 14597706990341803811657773)
                ·
                  refine ⟨5474140121378176429371665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14597706990341803811657773 5474140121378176429371665)
                  ·
                    refine ⟨4105605091033632322028749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474140121378176429371665 4105605091033632322028749)
                    ·
                      refine ⟨1539601909137612120760781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105605091033632322028749 1539601909137612120760781)
                      ·
                        rfl

theorem cell23_2998364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2998364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998364 prefixEnd_2998364 := by exact prefixLift 2998364
  have htrace : WordTrace (prefixWord ++ tailWord_2998364) baseStart_2998364 baseEnd_2998364 := by
    simpa [prefixWord, tailWord_2998364, baseEnd_2998364] using wordTrace_append hprefix tailTrace_2998364
  have hstable : (prefixWord ++ tailWord_2998364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998364).length < 2 ^ (prefixWord ++ tailWord_2998364).sum := by decide
  have hdescent : baseEnd_2998364 < baseStart_2998364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998378 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_2998378 : Nat := 118140960795 + 2998378 * 2 ^ 59
def prefixEnd_2998378 : Nat := 4983230072969 + 3 ^ 40 * 2998378 * 2
def baseEnd_2998378 : Nat := 1539609097866775065985717

theorem tailTrace_2998378 : CollatzResearch.WordTrace tailWord_2998378 prefixEnd_2998378 1539609097866775065985717 := by
  unfold tailWord_2998378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27339957482849015759640947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72906553287597375359042525 27339957482849015759640947)
  ·
    refine ⟨41009936224273523639461421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27339957482849015759640947 41009936224273523639461421)
    ·
      refine ⟨15378726084102571364798033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41009936224273523639461421 15378726084102571364798033)
      ·
        refine ⟨11534044563076928523598525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15378726084102571364798033 11534044563076928523598525)
        ·
          refine ⟨4325266711153848196349447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11534044563076928523598525 4325266711153848196349447)
          ·
            refine ⟨6487900066730772294524171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325266711153848196349447 6487900066730772294524171)
            ·
              refine ⟨9731850100096158441786257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487900066730772294524171 9731850100096158441786257)
              ·
                refine ⟨7298887575072118831339693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9731850100096158441786257 7298887575072118831339693)
                ·
                  refine ⟨2737082840652044561752385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7298887575072118831339693 2737082840652044561752385)
                  ·
                    refine ⟨2052812130489033421314289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2737082840652044561752385 2052812130489033421314289)
                    ·
                      refine ⟨1539609097866775065985717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052812130489033421314289 1539609097866775065985717)
                      ·
                        rfl

theorem cell23_2998378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_2998378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998378 prefixEnd_2998378 := by exact prefixLift 2998378
  have htrace : WordTrace (prefixWord ++ tailWord_2998378) baseStart_2998378 baseEnd_2998378 := by
    simpa [prefixWord, tailWord_2998378, baseEnd_2998378] using wordTrace_append hprefix tailTrace_2998378
  have hstable : (prefixWord ++ tailWord_2998378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998378).length < 2 ^ (prefixWord ++ tailWord_2998378).sum := by decide
  have hdescent : baseEnd_2998378 < baseStart_2998378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998422 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2998422 : Nat := 118140960795 + 2998422 * 2 ^ 59
def prefixEnd_2998422 : Nat := 4983230072969 + 3 ^ 40 * 2998422 * 2
def baseEnd_2998422 : Nat := 513210563671857631278505

theorem tailTrace_2998422 : CollatzResearch.WordTrace tailWord_2998422 prefixEnd_2998422 513210563671857631278505 := by
  unfold tailWord_2998422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835089671452291159572845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72907623162157772368777013 6835089671452291159572845)
  ·
    refine ⟨2563158626794609184839817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6835089671452291159572845 2563158626794609184839817)
    ·
      refine ⟨1922368970095956888629863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2563158626794609184839817 1922368970095956888629863)
      ·
        refine ⟨2883553455143935332944795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922368970095956888629863 2883553455143935332944795)
        ·
          refine ⟨4325330182715902999417193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883553455143935332944795 4325330182715902999417193)
          ·
            refine ⟨3243997637036927249562895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325330182715902999417193 3243997637036927249562895)
            ·
              refine ⟨4865996455555390874344343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243997637036927249562895 4865996455555390874344343)
              ·
                refine ⟨7298994683333086311516515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865996455555390874344343 7298994683333086311516515)
                ·
                  refine ⟨10948492024999629467274773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7298994683333086311516515 10948492024999629467274773)
                  ·
                    refine ⟨513210563671857631278505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10948492024999629467274773 513210563671857631278505)
                    ·
                      rfl

theorem cell23_2998422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2998422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998422 prefixEnd_2998422 := by exact prefixLift 2998422
  have htrace : WordTrace (prefixWord ++ tailWord_2998422) baseStart_2998422 baseEnd_2998422 := by
    simpa [prefixWord, tailWord_2998422, baseEnd_2998422] using wordTrace_append hprefix tailTrace_2998422
  have hstable : (prefixWord ++ tailWord_2998422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998422).length < 2 ^ (prefixWord ++ tailWord_2998422).sum := by decide
  have hdescent : baseEnd_2998422 < baseStart_2998422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998428 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2998428 : Nat := 118140960795 + 2998428 * 2 ^ 59
def prefixEnd_2998428 : Nat := 4983230072969 + 3 ^ 40 * 2998428 * 2
def baseEnd_2998428 : Nat := 1539634771899499870360487

theorem tailTrace_2998428 : CollatzResearch.WordTrace tailWord_2998428 prefixEnd_2998428 1539634771899499870360487 := by
  unfold tailWord_2998428
  simp only [CollatzResearch.WordTrace]
  refine ⟨54680826790607460788941969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72907769054143281051922625 54680826790607460788941969)
  ·
    refine ⟨41010620092955595591706477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54680826790607460788941969 41010620092955595591706477)
    ·
      refine ⟨15378982534858348346889929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41010620092955595591706477 15378982534858348346889929)
      ·
        refine ⟨11534236901143761260167447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15378982534858348346889929 11534236901143761260167447)
        ·
          refine ⟨17301355351715641890251171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534236901143761260167447 17301355351715641890251171)
          ·
            refine ⟨25952033027573462835376757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17301355351715641890251171 25952033027573462835376757)
            ·
              refine ⟨2433003096335012140816571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25952033027573462835376757 2433003096335012140816571)
              ·
                refine ⟨3649504644502518211224857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433003096335012140816571 3649504644502518211224857)
                ·
                  refine ⟨2737128483376888658418643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3649504644502518211224857 2737128483376888658418643)
                  ·
                    refine ⟨4105692725065332987627965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2737128483376888658418643 4105692725065332987627965)
                    ·
                      refine ⟨1539634771899499870360487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105692725065332987627965 1539634771899499870360487)
                      ·
                        rfl

theorem cell23_2998428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2998428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998428 prefixEnd_2998428 := by exact prefixLift 2998428
  have htrace : WordTrace (prefixWord ++ tailWord_2998428) baseStart_2998428 baseEnd_2998428 := by
    simpa [prefixWord, tailWord_2998428, baseEnd_2998428] using wordTrace_append hprefix tailTrace_2998428
  have hstable : (prefixWord ++ tailWord_2998428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998428).length < 2 ^ (prefixWord ++ tailWord_2998428).sum := by decide
  have hdescent : baseEnd_2998428 < baseStart_2998428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998437 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2998437 : Nat := 118140960795 + 2998437 * 2 ^ 59
def prefixEnd_2998437 : Nat := 4983230072969 + 3 ^ 40 * 2998437 * 2
def baseEnd_2998437 : Nat := 1539639393225390335147945

theorem tailTrace_2998437 : CollatzResearch.WordTrace tailWord_2998437 prefixEnd_2998437 1539639393225390335147945 := by
  unfold tailWord_2998437
  simp only [CollatzResearch.WordTrace]
  refine ⟨109361981838182316114961565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72907987892121544076641043 109361981838182316114961565)
  ·
    refine ⟨41010743189318368543110587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109361981838182316114961565 41010743189318368543110587)
    ·
      refine ⟨61516114783977552814665881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41010743189318368543110587 61516114783977552814665881)
      ·
        refine ⟨46137086087983164610999411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61516114783977552814665881 46137086087983164610999411)
        ·
          refine ⟨69205629131974746916499117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46137086087983164610999411 69205629131974746916499117)
          ·
            refine ⟨25952110924490530093687169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69205629131974746916499117 25952110924490530093687169)
            ·
              refine ⟨19464083193367897570265377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25952110924490530093687169 19464083193367897570265377)
              ·
                refine ⟨14598062395025923177699033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19464083193367897570265377 14598062395025923177699033)
                ·
                  refine ⟨10948546796269442383274275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14598062395025923177699033 10948546796269442383274275)
                  ·
                    refine ⟨16422820194404163574911413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10948546796269442383274275 16422820194404163574911413)
                    ·
                      refine ⟨1539639393225390335147945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16422820194404163574911413 1539639393225390335147945)
                      ·
                        rfl

theorem cell23_2998437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2998437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998437 prefixEnd_2998437 := by exact prefixLift 2998437
  have htrace : WordTrace (prefixWord ++ tailWord_2998437) baseStart_2998437 baseEnd_2998437 := by
    simpa [prefixWord, tailWord_2998437, baseEnd_2998437] using wordTrace_append hprefix tailTrace_2998437
  have hstable : (prefixWord ++ tailWord_2998437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998437).length < 2 ^ (prefixWord ++ tailWord_2998437).sum := by decide
  have hdescent : baseEnd_2998437 < baseStart_2998437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998446 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2998446 : Nat := 118140960795 + 2998446 * 2 ^ 59
def prefixEnd_2998446 : Nat := 4983230072969 + 3 ^ 40 * 2998446 * 2
def baseEnd_2998446 : Nat := 1539644014551280799935405

theorem tailTrace_2998446 : CollatzResearch.WordTrace tailWord_2998446 prefixEnd_2998446 1539644014551280799935405 := by
  unfold tailWord_2998446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13670288761893713831504899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72908206730099807101359461 13670288761893713831504899)
  ·
    refine ⟨20505433142840570747257349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13670288761893713831504899 20505433142840570747257349)
    ·
      refine ⟨3844768714282607015110753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20505433142840570747257349 3844768714282607015110753)
      ·
        refine ⟨2883576535711955261333065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3844768714282607015110753 2883576535711955261333065)
        ·
          refine ⟨2162682401783966445999799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2883576535711955261333065 2162682401783966445999799)
          ·
            refine ⟨3244023602675949668999699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162682401783966445999799 3244023602675949668999699)
            ·
              refine ⟨4866035404013924503499549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244023602675949668999699 4866035404013924503499549)
              ·
                refine ⟨1824763276505221688812331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866035404013924503499549 1824763276505221688812331)
                ·
                  refine ⟨2737144914757832533218497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824763276505221688812331 2737144914757832533218497)
                  ·
                    refine ⟨2052858686068374399913873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2737144914757832533218497 2052858686068374399913873)
                    ·
                      refine ⟨1539644014551280799935405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052858686068374399913873 1539644014551280799935405)
                      ·
                        rfl

theorem cell23_2998446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2998446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998446 prefixEnd_2998446 := by exact prefixLift 2998446
  have htrace : WordTrace (prefixWord ++ tailWord_2998446) baseStart_2998446 baseEnd_2998446 := by
    simpa [prefixWord, tailWord_2998446, baseEnd_2998446] using wordTrace_append hprefix tailTrace_2998446
  have hstable : (prefixWord ++ tailWord_2998446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998446).length < 2 ^ (prefixWord ++ tailWord_2998446).sum := by decide
  have hdescent : baseEnd_2998446 < baseStart_2998446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998468 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_2998468 : Nat := 118140960795 + 2998468 * 2 ^ 59
def prefixEnd_2998468 : Nat := 4983230072969 + 3 ^ 40 * 2998468 * 2
def baseEnd_2998468 : Nat := 1539655311125679713860303

theorem tailTrace_2998468 : CollatzResearch.WordTrace tailWord_2998468 prefixEnd_2998468 1539655311125679713860303 := by
  unfold tailWord_2998468
  simp only [CollatzResearch.WordTrace]
  refine ⟨54681556250535004204670029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72908741667380005606226705 54681556250535004204670029)
  ·
    refine ⟨20505583593950626576751261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54681556250535004204670029 20505583593950626576751261)
    ·
      refine ⟨7689593847731484966281723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20505583593950626576751261 7689593847731484966281723)
      ·
        refine ⟨11534390771597227449422585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689593847731484966281723 11534390771597227449422585)
        ·
          refine ⟨8650793078697920587066939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11534390771597227449422585 8650793078697920587066939)
          ·
            refine ⟨12976189618046880880600409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650793078697920587066939 12976189618046880880600409)
            ·
              refine ⟨9732142213535160660450307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12976189618046880880600409 9732142213535160660450307)
              ·
                refine ⟨14598213320302740990675461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732142213535160660450307 14598213320302740990675461)
                ·
                  refine ⟨2737164997556763935751649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14598213320302740990675461 2737164997556763935751649)
                  ·
                    refine ⟨2052873748167572951813737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2737164997556763935751649 2052873748167572951813737)
                    ·
                      refine ⟨1539655311125679713860303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052873748167572951813737 1539655311125679713860303)
                      ·
                        rfl

theorem cell23_2998468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_2998468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998468 prefixEnd_2998468 := by exact prefixLift 2998468
  have htrace : WordTrace (prefixWord ++ tailWord_2998468) baseStart_2998468 baseEnd_2998468 := by
    simpa [prefixWord, tailWord_2998468, baseEnd_2998468] using wordTrace_append hprefix tailTrace_2998468
  have hstable : (prefixWord ++ tailWord_2998468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998468).length < 2 ^ (prefixWord ++ tailWord_2998468).sum := by decide
  have hdescent : baseEnd_2998468 < baseStart_2998468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998485 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2998485 : Nat := 118140960795 + 2998485 * 2 ^ 59
def prefixEnd_2998485 : Nat := 4983230072969 + 3 ^ 40 * 2998485 * 2
def baseEnd_2998485 : Nat := 1539664040296806147347725

theorem tailTrace_2998485 : CollatzResearch.WordTrace tailWord_2998485 prefixEnd_2998485 1539664040296806147347725 := by
  unfold tailWord_2998485
  simp only [CollatzResearch.WordTrace]
  refine ⟨109363732542008420312708909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72909155028005613541805939 109363732542008420312708909)
  ·
    refine ⟨41011399703253157617265841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109363732542008420312708909 41011399703253157617265841)
    ·
      refine ⟨30758549777439868212949381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41011399703253157617265841 30758549777439868212949381)
      ·
        refine ⟨5767228083269975289928009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30758549777439868212949381 5767228083269975289928009)
        ·
          refine ⟨4325421062452481467446007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5767228083269975289928009 4325421062452481467446007)
          ·
            refine ⟨6488131593678722201169011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325421062452481467446007 6488131593678722201169011)
            ·
              refine ⟨9732197390518083301753517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488131593678722201169011 9732197390518083301753517)
              ·
                refine ⟨3649574021444281238157569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9732197390518083301753517 3649574021444281238157569)
                ·
                  refine ⟨2737180516083210928618177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3649574021444281238157569 2737180516083210928618177)
                  ·
                    refine ⟨2052885387062408196463633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2737180516083210928618177 2052885387062408196463633)
                    ·
                      refine ⟨1539664040296806147347725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2052885387062408196463633 1539664040296806147347725)
                      ·
                        rfl

theorem cell23_2998485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2998485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998485 prefixEnd_2998485 := by exact prefixLift 2998485
  have htrace : WordTrace (prefixWord ++ tailWord_2998485) baseStart_2998485 baseEnd_2998485 := by
    simpa [prefixWord, tailWord_2998485, baseEnd_2998485] using wordTrace_append hprefix tailTrace_2998485
  have hstable : (prefixWord ++ tailWord_2998485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998485).length < 2 ^ (prefixWord ++ tailWord_2998485).sum := by decide
  have hdescent : baseEnd_2998485 < baseStart_2998485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998487 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 6, 5]
def baseStart_2998487 : Nat := 118140960795 + 2998487 * 2 ^ 59
def prefixEnd_2998487 : Nat := 4983230072969 + 3 ^ 40 * 2998487 * 2
def baseEnd_2998487 : Nat := 513221689086038379840905

theorem tailTrace_2998487 : CollatzResearch.WordTrace tailWord_2998487 prefixEnd_2998487 513221689086038379840905 := by
  unfold tailWord_2998487
  simp only [CollatzResearch.WordTrace]
  refine ⟨109363805488001174654281715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72909203658667449769521143 109363805488001174654281715)
  ·
    refine ⟨164045708232001761981422573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109363805488001174654281715 164045708232001761981422573)
    ·
      refine ⟨61517140587000660743033465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164045708232001761981422573 61517140587000660743033465)
      ·
        refine ⟨46137855440250495557275099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61517140587000660743033465 46137855440250495557275099)
        ·
          refine ⟨69206783160375743335912649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46137855440250495557275099 69206783160375743335912649)
          ·
            refine ⟨51905087370281807501934487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69206783160375743335912649 51905087370281807501934487)
            ·
              refine ⟨77857631055422711252901731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51905087370281807501934487 77857631055422711252901731)
              ·
                refine ⟨116786446583134066879352597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77857631055422711252901731 116786446583134066879352597)
                ·
                  refine ⟨5474364683584409384969653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116786446583134066879352597 5474364683584409384969653)
                  ·
                    refine ⟨513221689086038379840905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5474364683584409384969653 513221689086038379840905)
                    ·
                      rfl

theorem cell23_2998487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_2998487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998487 prefixEnd_2998487 := by exact prefixLift 2998487
  have htrace : WordTrace (prefixWord ++ tailWord_2998487) baseStart_2998487 baseEnd_2998487 := by
    simpa [prefixWord, tailWord_2998487, baseEnd_2998487] using wordTrace_append hprefix tailTrace_2998487
  have hstable : (prefixWord ++ tailWord_2998487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998487).length < 2 ^ (prefixWord ++ tailWord_2998487).sum := by decide
  have hdescent : baseEnd_2998487 < baseStart_2998487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998497 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2998497 : Nat := 118140960795 + 2998497 * 2 ^ 59
def prefixEnd_2998497 : Nat := 4983230072969 + 3 ^ 40 * 2998497 * 2
def baseEnd_2998497 : Nat := 1539670202064660100397669

theorem tailTrace_2998497 : CollatzResearch.WordTrace tailWord_2998497 prefixEnd_2998497 1539670202064660100397669 := by
  unfold tailWord_2998497
  simp only [CollatzResearch.WordTrace]
  refine ⟨109364170217964946362145745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72909446811976630908097163 109364170217964946362145745)
  ·
    refine ⟨82023127663473709771609309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109364170217964946362145745 82023127663473709771609309)
    ·
      refine ⟨30758672873802641164353491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82023127663473709771609309 30758672873802641164353491)
      ·
        refine ⟨46138009310703961746530237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30758672873802641164353491 46138009310703961746530237)
        ·
          refine ⟨17301753491513985654948839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46138009310703961746530237 17301753491513985654948839)
          ·
            refine ⟨25952630237270978482423259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17301753491513985654948839 25952630237270978482423259)
            ·
              refine ⟨38928945355906467723634889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25952630237270978482423259 38928945355906467723634889)
              ·
                refine ⟨29196709016929850792726167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38928945355906467723634889 29196709016929850792726167)
                ·
                  refine ⟨43795063525394776189089251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29196709016929850792726167 43795063525394776189089251)
                  ·
                    refine ⟨65692595288092164283633877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43795063525394776189089251 65692595288092164283633877)
                    ·
                      refine ⟨1539670202064660100397669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65692595288092164283633877 1539670202064660100397669)
                      ·
                        rfl

theorem cell23_2998497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2998497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998497 prefixEnd_2998497 := by exact prefixLift 2998497
  have htrace : WordTrace (prefixWord ++ tailWord_2998497) baseStart_2998497 baseEnd_2998497 := by
    simpa [prefixWord, tailWord_2998497, baseEnd_2998497] using wordTrace_append hprefix tailTrace_2998497
  have hstable : (prefixWord ++ tailWord_2998497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998497).length < 2 ^ (prefixWord ++ tailWord_2998497).sum := by decide
  have hdescent : baseEnd_2998497 < baseStart_2998497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998504 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2998504 : Nat := 118140960795 + 2998504 * 2 ^ 59
def prefixEnd_2998504 : Nat := 4983230072969 + 3 ^ 40 * 2998504 * 2
def baseEnd_2998504 : Nat := 513224598809747191003379

theorem tailTrace_2998504 : CollatzResearch.WordTrace tailWord_2998504 prefixEnd_2998504 513224598809747191003379 := by
  unfold tailWord_2998504
  simp only [CollatzResearch.WordTrace]
  refine ⟨54682212764469793278825283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72909617019293057705100377 54682212764469793278825283)
  ·
    refine ⟨82023319146704689918237925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54682212764469793278825283 82023319146704689918237925)
    ·
      refine ⟨15379372340007129359669611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82023319146704689918237925 15379372340007129359669611)
      ·
        refine ⟨23069058510010694039504417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15379372340007129359669611 23069058510010694039504417)
        ·
          refine ⟨17301793882508020529628313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23069058510010694039504417 17301793882508020529628313)
          ·
            refine ⟨12976345411881015397221235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17301793882508020529628313 12976345411881015397221235)
            ·
              refine ⟨19464518117821523095831853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976345411881015397221235 19464518117821523095831853)
              ·
                refine ⟨7299194294183071160936945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19464518117821523095831853 7299194294183071160936945)
                ·
                  refine ⟨5474395720637303370702709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7299194294183071160936945 5474395720637303370702709)
                  ·
                    refine ⟨513224598809747191003379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5474395720637303370702709 513224598809747191003379)
                    ·
                      rfl

theorem cell23_2998504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2998504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998504 prefixEnd_2998504 := by exact prefixLift 2998504
  have htrace : WordTrace (prefixWord ++ tailWord_2998504) baseStart_2998504 baseEnd_2998504 := by
    simpa [prefixWord, tailWord_2998504, baseEnd_2998504] using wordTrace_append hprefix tailTrace_2998504
  have hstable : (prefixWord ++ tailWord_2998504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998504).length < 2 ^ (prefixWord ++ tailWord_2998504).sum := by decide
  have hdescent : baseEnd_2998504 < baseStart_2998504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998514 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2998514 : Nat := 118140960795 + 2998514 * 2 ^ 59
def prefixEnd_2998514 : Nat := 4983230072969 + 3 ^ 40 * 2998514 * 2
def baseEnd_2998514 : Nat := 1539678931235786533885091

theorem tailTrace_2998514 : CollatzResearch.WordTrace tailWord_2998514 prefixEnd_2998514 1539678931235786533885091 := by
  unfold tailWord_2998514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27341197564725839566378649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72909860172602238843676397 27341197564725839566378649)
  ·
    refine ⟨20505898173544379674783987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27341197564725839566378649 20505898173544379674783987)
    ·
      refine ⟨30758847260316569512175981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20505898173544379674783987 30758847260316569512175981)
      ·
        refine ⟨11534567722618713567065993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30758847260316569512175981 11534567722618713567065993)
        ·
          refine ⟨8650925791964035175299495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11534567722618713567065993 8650925791964035175299495)
          ·
            refine ⟨12976388687946052762949243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650925791964035175299495 12976388687946052762949243)
            ·
              refine ⟨19464583031919079144423865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976388687946052762949243 19464583031919079144423865)
              ·
                refine ⟨14598437273939309358317899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19464583031919079144423865 14598437273939309358317899)
                ·
                  refine ⟨21897655910908964037476849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14598437273939309358317899 21897655910908964037476849)
                  ·
                    refine ⟨16423241933181723028107637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21897655910908964037476849 16423241933181723028107637)
                    ·
                      refine ⟨1539678931235786533885091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16423241933181723028107637 1539678931235786533885091)
                      ·
                        rfl

theorem cell23_2998514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2998514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998514 prefixEnd_2998514 := by exact prefixLift 2998514
  have htrace : WordTrace (prefixWord ++ tailWord_2998514) baseStart_2998514 baseEnd_2998514 := by
    simpa [prefixWord, tailWord_2998514, baseEnd_2998514] using wordTrace_append hprefix tailTrace_2998514
  have hstable : (prefixWord ++ tailWord_2998514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998514).length < 2 ^ (prefixWord ++ tailWord_2998514).sum := by decide
  have hdescent : baseEnd_2998514 < baseStart_2998514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998527 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_2998527 : Nat := 118140960795 + 2998527 * 2 ^ 59
def prefixEnd_2998527 : Nat := 4983230072969 + 3 ^ 40 * 2998527 * 2
def baseEnd_2998527 : Nat := 1539685606484294983022531

theorem tailTrace_2998527 : CollatzResearch.WordTrace tailWord_2998527 prefixEnd_2998527 1539685606484294983022531 := by
  unfold tailWord_2998527
  simp only [CollatzResearch.WordTrace]
  refine ⟨109365264407856261485737835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72910176271904174323825223 109365264407856261485737835)
  ·
    refine ⟨164047896611784392228606753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109365264407856261485737835 164047896611784392228606753)
    ·
      refine ⟨123035922458838294171455065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164047896611784392228606753 123035922458838294171455065)
      ·
        refine ⟨92276941844128720628591299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123035922458838294171455065 92276941844128720628591299)
        ·
          refine ⟨138415412766193080942886949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92276941844128720628591299 138415412766193080942886949)
          ·
            refine ⟨25952889893661202676791303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138415412766193080942886949 25952889893661202676791303)
            ·
              refine ⟨38929334840491804015186955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25952889893661202676791303 38929334840491804015186955)
              ·
                refine ⟨58394002260737706022780433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38929334840491804015186955 58394002260737706022780433)
                ·
                  refine ⟨43795501695553279517085325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58394002260737706022780433 43795501695553279517085325)
                  ·
                    refine ⟨16423313135832479818906997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43795501695553279517085325 16423313135832479818906997)
                    ·
                      refine ⟨1539685606484294983022531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16423313135832479818906997 1539685606484294983022531)
                      ·
                        rfl

theorem cell23_2998527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_2998527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998527 prefixEnd_2998527 := by exact prefixLift 2998527
  have htrace : WordTrace (prefixWord ++ tailWord_2998527) baseStart_2998527 baseEnd_2998527 := by
    simpa [prefixWord, tailWord_2998527, baseEnd_2998527] using wordTrace_append hprefix tailTrace_2998527
  have hstable : (prefixWord ++ tailWord_2998527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998527).length < 2 ^ (prefixWord ++ tailWord_2998527).sum := by decide
  have hdescent : baseEnd_2998527 < baseStart_2998527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998551 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 3, 4]
def baseStart_2998551 : Nat := 118140960795 + 2998551 * 2 ^ 59
def prefixEnd_2998551 : Nat := 4983230072969 + 3 ^ 40 * 2998551 * 2
def baseEnd_2998551 : Nat := 513232643340000963040807

theorem tailTrace_2998551 : CollatzResearch.WordTrace tailWord_2998551 prefixEnd_2998551 513232643340000963040807 := by
  unfold tailWord_2998551
  simp only [CollatzResearch.WordTrace]
  refine ⟨109366139759769313584611507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72910759839846209056407671 109366139759769313584611507)
  ·
    refine ⟨164049209639653970376917261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109366139759769313584611507 164049209639653970376917261)
    ·
      refine ⟨61518453614870238891343973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164049209639653970376917261 61518453614870238891343973)
      ·
        refine ⟨11534710052788169792126995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61518453614870238891343973 11534710052788169792126995)
        ·
          refine ⟨17302065079182254688190493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534710052788169792126995 17302065079182254688190493)
          ·
            refine ⟨6488274404693345508071435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17302065079182254688190493 6488274404693345508071435)
            ·
              refine ⟨9732411607040018262107153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488274404693345508071435 9732411607040018262107153)
              ·
                refine ⟨7299308705280013696580365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9732411607040018262107153 7299308705280013696580365)
                ·
                  refine ⟨2737240764480005136217637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7299308705280013696580365 2737240764480005136217637)
                  ·
                    refine ⟨513232643340000963040807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2737240764480005136217637 513232643340000963040807)
                    ·
                      rfl

theorem cell23_2998551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_2998551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998551 prefixEnd_2998551 := by exact prefixLift 2998551
  have htrace : WordTrace (prefixWord ++ tailWord_2998551) baseStart_2998551 baseEnd_2998551 := by
    simpa [prefixWord, tailWord_2998551, baseEnd_2998551] using wordTrace_append hprefix tailTrace_2998551
  have hstable : (prefixWord ++ tailWord_2998551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998551).length < 2 ^ (prefixWord ++ tailWord_2998551).sum := by decide
  have hdescent : baseEnd_2998551 < baseStart_2998551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998558 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2998558 : Nat := 118140960795 + 2998558 * 2 ^ 59
def prefixEnd_2998558 : Nat := 4983230072969 + 3 ^ 40 * 2998558 * 2
def baseEnd_2998558 : Nat := 1539701524384584361734889

theorem tailTrace_2998558 : CollatzResearch.WordTrace tailWord_2998558 prefixEnd_2998558 1539701524384584361734889 := by
  unfold tailWord_2998558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13670799383842994222514541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72910930047162635853410885 13670799383842994222514541)
  ·
    refine ⟨5126549768941122833442953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13670799383842994222514541 5126549768941122833442953)
    ·
      refine ⟨3844912326705842125082215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5126549768941122833442953 3844912326705842125082215)
      ·
        refine ⟨5767368490058763187623323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844912326705842125082215 5767368490058763187623323)
        ·
          refine ⟨8651052735088144781434985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767368490058763187623323 8651052735088144781434985)
          ·
            refine ⟨6488289551316108586076239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651052735088144781434985 6488289551316108586076239)
            ·
              refine ⟨9732434326974162879114359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488289551316108586076239 9732434326974162879114359)
              ·
                refine ⟨14598651490461244318671539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732434326974162879114359 14598651490461244318671539)
                ·
                  refine ⟨21897977235691866478007309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14598651490461244318671539 21897977235691866478007309)
                  ·
                    refine ⟨8211741463384449929252741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21897977235691866478007309 8211741463384449929252741)
                    ·
                      refine ⟨1539701524384584361734889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8211741463384449929252741 1539701524384584361734889)
                      ·
                        rfl

theorem cell23_2998558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2998558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998558 prefixEnd_2998558 := by exact prefixLift 2998558
  have htrace : WordTrace (prefixWord ++ tailWord_2998558) baseStart_2998558 baseEnd_2998558 := by
    simpa [prefixWord, tailWord_2998558, baseEnd_2998558] using wordTrace_append hprefix tailTrace_2998558
  have hstable : (prefixWord ++ tailWord_2998558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998558).length < 2 ^ (prefixWord ++ tailWord_2998558).sum := by decide
  have hdescent : baseEnd_2998558 < baseStart_2998558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998561 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2998561 : Nat := 118140960795 + 2998561 * 2 ^ 59
def prefixEnd_2998561 : Nat := 4983230072969 + 3 ^ 40 * 2998561 * 2
def baseEnd_2998561 : Nat := 1539703064826547849997375

theorem tailTrace_2998561 : CollatzResearch.WordTrace tailWord_2998561 prefixEnd_2998561 1539703064826547849997375 := by
  unfold tailWord_2998561
  simp only [CollatzResearch.WordTrace]
  refine ⟨109366504489733085292475537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72911002993155390194983691 109366504489733085292475537)
  ·
    refine ⟨82024878367299813969356653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109366504489733085292475537 82024878367299813969356653)
    ·
      refine ⟨30759329387737430238508745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82024878367299813969356653 30759329387737430238508745)
      ·
        refine ⟨23069497040803072678881559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30759329387737430238508745 23069497040803072678881559)
        ·
          refine ⟨34604245561204609018322339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23069497040803072678881559 34604245561204609018322339)
          ·
            refine ⟨51906368341806913527483509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34604245561204609018322339 51906368341806913527483509)
            ·
              refine ⟨4866222032044398143201579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51906368341806913527483509 4866222032044398143201579)
              ·
                refine ⟨7299333048066597214802369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866222032044398143201579 7299333048066597214802369)
                ·
                  refine ⟨5474499786049947911101777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7299333048066597214802369 5474499786049947911101777)
                  ·
                    refine ⟨4105874839537460933326333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474499786049947911101777 4105874839537460933326333)
                    ·
                      refine ⟨1539703064826547849997375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105874839537460933326333 1539703064826547849997375)
                      ·
                        rfl

theorem cell23_2998561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2998561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998561 prefixEnd_2998561 := by exact prefixLift 2998561
  have htrace : WordTrace (prefixWord ++ tailWord_2998561) baseStart_2998561 baseEnd_2998561 := by
    simpa [prefixWord, tailWord_2998561, baseEnd_2998561] using wordTrace_append hprefix tailTrace_2998561
  have hstable : (prefixWord ++ tailWord_2998561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998561).length < 2 ^ (prefixWord ++ tailWord_2998561).sum := by decide
  have hdescent : baseEnd_2998561 < baseStart_2998561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998641 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 2, 4]
def baseStart_2998641 : Nat := 118140960795 + 2998641 * 2 ^ 59
def prefixEnd_2998641 : Nat := 4983230072969 + 3 ^ 40 * 2998641 * 2
def baseEnd_2998641 : Nat := 513248047759635845665669

theorem tailTrace_2998641 : CollatzResearch.WordTrace tailWord_2998641 prefixEnd_2998641 513248047759635845665669 := by
  unfold tailWord_2998641
  simp only [CollatzResearch.WordTrace]
  refine ⟨109369422329443258955387777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72912948219628839303591851 109369422329443258955387777)
  ·
    refine ⟨82027066747082444216540833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109369422329443258955387777 82027066747082444216540833)
    ·
      refine ⟨61520300060311833162405625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82027066747082444216540833 61520300060311833162405625)
      ·
        refine ⟨46140225045233874871804219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61520300060311833162405625 46140225045233874871804219)
        ·
          refine ⟨69210337567850812307706329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46140225045233874871804219 69210337567850812307706329)
          ·
            refine ⟨51907753175888109230779747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69210337567850812307706329 51907753175888109230779747)
            ·
              refine ⟨77861629763832163846169621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51907753175888109230779747 77861629763832163846169621)
              ·
                refine ⟨3649763895179632680289201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77861629763832163846169621 3649763895179632680289201)
                ·
                  refine ⟨2737322921384724510216901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3649763895179632680289201 2737322921384724510216901)
                  ·
                    refine ⟨513248047759635845665669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2737322921384724510216901 513248047759635845665669)
                    ·
                      rfl

theorem cell23_2998641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_2998641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998641 prefixEnd_2998641 := by exact prefixLift 2998641
  have htrace : WordTrace (prefixWord ++ tailWord_2998641) baseStart_2998641 baseEnd_2998641 := by
    simpa [prefixWord, tailWord_2998641, baseEnd_2998641] using wordTrace_append hprefix tailTrace_2998641
  have hstable : (prefixWord ++ tailWord_2998641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998641).length < 2 ^ (prefixWord ++ tailWord_2998641).sum := by decide
  have hdescent : baseEnd_2998641 < baseStart_2998641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998642 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_2998642 : Nat := 118140960795 + 2998642 * 2 ^ 59
def prefixEnd_2998642 : Nat := 4983230072969 + 3 ^ 40 * 2998642 * 2
def baseEnd_2998642 : Nat := 1539744656759562033084503

theorem tailTrace_2998642 : CollatzResearch.WordTrace tailWord_2998642 prefixEnd_2998642 1539744656759562033084503 := by
  unfold tailWord_2998642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27342364700609909031543545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72912972534959757417449453 27342364700609909031543545)
  ·
    refine ⟨20506773525457431773657659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27342364700609909031543545 20506773525457431773657659)
    ·
      refine ⟨30760160288186147660486489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20506773525457431773657659 30760160288186147660486489)
      ·
        refine ⟨23070120216139610745364867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30760160288186147660486489 23070120216139610745364867)
        ·
          refine ⟨34605180324209416118047301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23070120216139610745364867 34605180324209416118047301)
          ·
            refine ⟨6488471310789265522133869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34605180324209416118047301 6488471310789265522133869)
            ·
              refine ⟨2433176741545974570800201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6488471310789265522133869 2433176741545974570800201)
              ·
                refine ⟨1824882556159480928100151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433176741545974570800201 1824882556159480928100151)
                ·
                  refine ⟨2737323834239221392150227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824882556159480928100151 2737323834239221392150227)
                  ·
                    refine ⟨4105985751358832088225341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2737323834239221392150227 4105985751358832088225341)
                    ·
                      refine ⟨1539744656759562033084503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4105985751358832088225341 1539744656759562033084503)
                      ·
                        rfl

theorem cell23_2998642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_2998642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998642 prefixEnd_2998642 := by exact prefixLift 2998642
  have htrace : WordTrace (prefixWord ++ tailWord_2998642) baseStart_2998642 baseEnd_2998642 := by
    simpa [prefixWord, tailWord_2998642, baseEnd_2998642] using wordTrace_append hprefix tailTrace_2998642
  have hstable : (prefixWord ++ tailWord_2998642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998642).length < 2 ^ (prefixWord ++ tailWord_2998642).sum := by decide
  have hdescent : baseEnd_2998642 < baseStart_2998642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998668 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_2998668 : Nat := 118140960795 + 2998668 * 2 ^ 59
def prefixEnd_2998668 : Nat := 4983230072969 + 3 ^ 40 * 2998668 * 2
def baseEnd_2998668 : Nat := 1539758007256578931359383

theorem tailTrace_2998668 : CollatzResearch.WordTrace tailWord_2998668 prefixEnd_2998668 1539758007256578931359383 := by
  unfold tailWord_2998668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54685203550172721283310329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72913604733563628377747105 54685203550172721283310329)
  ·
    refine ⟨41013902662629540962482747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54685203550172721283310329 41013902662629540962482747)
    ·
      refine ⟨61520853993944311443724121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41013902662629540962482747 61520853993944311443724121)
      ·
        refine ⟨46140640495458233582793091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61520853993944311443724121 46140640495458233582793091)
        ·
          refine ⟨69210960743187350374189637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46140640495458233582793091 69210960743187350374189637)
          ·
            refine ⟨12977055139347628195160557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69210960743187350374189637 12977055139347628195160557)
            ·
              refine ⟨4866395677255360573185209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12977055139347628195160557 4866395677255360573185209)
              ·
                refine ⟨3649796757941520429888907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4866395677255360573185209 3649796757941520429888907)
                ·
                  refine ⟨5474695136912280644833361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649796757941520429888907 5474695136912280644833361)
                  ·
                    refine ⟨4106021352684210483625021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474695136912280644833361 4106021352684210483625021)
                    ·
                      refine ⟨1539758007256578931359383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106021352684210483625021 1539758007256578931359383)
                      ·
                        rfl

theorem cell23_2998668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_2998668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998668 prefixEnd_2998668 := by exact prefixLift 2998668
  have htrace : WordTrace (prefixWord ++ tailWord_2998668) baseStart_2998668 baseEnd_2998668 := by
    simpa [prefixWord, tailWord_2998668, baseEnd_2998668] using wordTrace_append hprefix tailTrace_2998668
  have hstable : (prefixWord ++ tailWord_2998668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998668).length < 2 ^ (prefixWord ++ tailWord_2998668).sum := by decide
  have hdescent : baseEnd_2998668 < baseStart_2998668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998681 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_2998681 : Nat := 118140960795 + 2998681 * 2 ^ 59
def prefixEnd_2998681 : Nat := 4983230072969 + 3 ^ 40 * 2998681 * 2
def baseEnd_2998681 : Nat := 1539764682505087380496823

theorem tailTrace_2998681 : CollatzResearch.WordTrace tailWord_2998681 prefixEnd_2998681 1539764682505087380496823 := by
  unfold tailWord_2998681
  simp only [CollatzResearch.WordTrace]
  refine ⟨109370881249298345786843897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72913920832865563857895931 109370881249298345786843897)
  ·
    refine ⟨82028160936973759340132923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109370881249298345786843897 82028160936973759340132923)
    ·
      refine ⟨123042241405460639010199385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82028160936973759340132923 123042241405460639010199385)
      ·
        refine ⟨92281681054095479257649539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123042241405460639010199385 92281681054095479257649539)
        ·
          refine ⟨138422521581143218886474309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92281681054095479257649539 138422521581143218886474309)
          ·
            refine ⟨25954222796464353541213933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138422521581143218886474309 25954222796464353541213933)
            ·
              refine ⟨9732833548674132577955225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25954222796464353541213933 9732833548674132577955225)
              ·
                refine ⟨7299625161505599433466419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9732833548674132577955225 7299625161505599433466419)
                ·
                  refine ⟨10949437742258399150199629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7299625161505599433466419 10949437742258399150199629)
                  ·
                    refine ⟨4106039153346899681324861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10949437742258399150199629 4106039153346899681324861)
                    ·
                      refine ⟨1539764682505087380496823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106039153346899681324861 1539764682505087380496823)
                      ·
                        rfl

theorem cell23_2998681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_2998681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998681 prefixEnd_2998681 := by exact prefixLift 2998681
  have htrace : WordTrace (prefixWord ++ tailWord_2998681) baseStart_2998681 baseEnd_2998681 := by
    simpa [prefixWord, tailWord_2998681, baseEnd_2998681] using wordTrace_append hprefix tailTrace_2998681
  have hstable : (prefixWord ++ tailWord_2998681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998681).length < 2 ^ (prefixWord ++ tailWord_2998681).sum := by decide
  have hdescent : baseEnd_2998681 < baseStart_2998681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998685 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_2998685 : Nat := 118140960795 + 2998685 * 2 ^ 59
def prefixEnd_2998685 : Nat := 4983230072969 + 3 ^ 40 * 2998685 * 2
def baseEnd_2998685 : Nat := 1539766736427705364846805

theorem tailTrace_2998685 : CollatzResearch.WordTrace tailWord_2998685 prefixEnd_2998685 1539766736427705364846805 := by
  unfold tailWord_2998685
  simp only [CollatzResearch.WordTrace]
  refine ⟨109371027141283854469989509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72914018094189236313326339 109371027141283854469989509)
  ·
    refine ⟨20507067588990722713123033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109371027141283854469989509 20507067588990722713123033)
    ·
      refine ⟨15380300691743042034842275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20507067588990722713123033 15380300691743042034842275)
      ·
        refine ⟨23070451037614563052263413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15380300691743042034842275 23070451037614563052263413)
        ·
          refine ⟨2162854784776365286149695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23070451037614563052263413 2162854784776365286149695)
          ·
            refine ⟨3244282177164547929224543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162854784776365286149695 3244282177164547929224543)
            ·
              refine ⟨4866423265746821893836815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244282177164547929224543 4866423265746821893836815)
              ·
                refine ⟨7299634898620232840755223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866423265746821893836815 7299634898620232840755223)
                ·
                  refine ⟨10949452347930349261132835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7299634898620232840755223 10949452347930349261132835)
                  ·
                    refine ⟨16424178521895523891699253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10949452347930349261132835 16424178521895523891699253)
                    ·
                      refine ⟨1539766736427705364846805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16424178521895523891699253 1539766736427705364846805)
                      ·
                        rfl

theorem cell23_2998685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_2998685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998685 prefixEnd_2998685 := by exact prefixLift 2998685
  have htrace : WordTrace (prefixWord ++ tailWord_2998685) baseStart_2998685 baseEnd_2998685 := by
    simpa [prefixWord, tailWord_2998685, baseEnd_2998685] using wordTrace_append hprefix tailTrace_2998685
  have hstable : (prefixWord ++ tailWord_2998685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998685).length < 2 ^ (prefixWord ++ tailWord_2998685).sum := by decide
  have hdescent : baseEnd_2998685 < baseStart_2998685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998742 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_2998742 : Nat := 118140960795 + 2998742 * 2 ^ 59
def prefixEnd_2998742 : Nat := 4983230072969 + 3 ^ 40 * 2998742 * 2
def baseEnd_2998742 : Nat := 1539796004825011641834043

theorem tailTrace_2998742 : CollatzResearch.WordTrace tailWord_2998742 prefixEnd_2998742 1539796004825011641834043 := by
  unfold tailWord_2998742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835819131379834575300905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72915404068051568803209653 6835819131379834575300905)
  ·
    refine ⟨5126864348534875931475679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6835819131379834575300905 5126864348534875931475679)
    ·
      refine ⟨7690296522802313897213519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5126864348534875931475679 7690296522802313897213519)
      ·
        refine ⟨11535444784203470845820279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7690296522802313897213519 11535444784203470845820279)
        ·
          refine ⟨17303167176305206268730419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11535444784203470845820279 17303167176305206268730419)
          ·
            refine ⟨25954750764457809403095629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17303167176305206268730419 25954750764457809403095629)
            ·
              refine ⟨9733031536671678526160861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25954750764457809403095629 9733031536671678526160861)
              ·
                refine ⟨3649886826251879447310323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9733031536671678526160861 3649886826251879447310323)
                ·
                  refine ⟨5474830239377819170965485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649886826251879447310323 5474830239377819170965485)
                  ·
                    refine ⟨2053061339766682189112057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5474830239377819170965485 2053061339766682189112057)
                    ·
                      refine ⟨1539796004825011641834043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053061339766682189112057 1539796004825011641834043)
                      ·
                        rfl

theorem cell23_2998742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_2998742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998742 prefixEnd_2998742 := by exact prefixLift 2998742
  have htrace : WordTrace (prefixWord ++ tailWord_2998742) baseStart_2998742 baseEnd_2998742 := by
    simpa [prefixWord, tailWord_2998742, baseEnd_2998742] using wordTrace_append hprefix tailTrace_2998742
  have hstable : (prefixWord ++ tailWord_2998742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998742).length < 2 ^ (prefixWord ++ tailWord_2998742).sum := by decide
  have hdescent : baseEnd_2998742 < baseStart_2998742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998744 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 11]
def baseStart_2998744 : Nat := 118140960795 + 2998744 * 2 ^ 59
def prefixEnd_2998744 : Nat := 4983230072969 + 3 ^ 40 * 2998744 * 2
def baseEnd_2998744 : Nat := 171088559087368959334337

theorem tailTrace_2998744 : CollatzResearch.WordTrace tailWord_2998744 prefixEnd_2998744 171088559087368959334337 := by
  unfold tailWord_2998744
  simp only [CollatzResearch.WordTrace]
  refine ⟨54686589524035053773193643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72915452698713405030924857 54686589524035053773193643)
  ·
    refine ⟨82029884286052580659790465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54686589524035053773193643 82029884286052580659790465)
    ·
      refine ⟨61522413214539435494842849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82029884286052580659790465 61522413214539435494842849)
      ·
        refine ⟨46141809910904576621132137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61522413214539435494842849 46141809910904576621132137)
        ·
          refine ⟨34606357433178432465849103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46141809910904576621132137 34606357433178432465849103)
          ·
            refine ⟨51909536149767648698773655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34606357433178432465849103 51909536149767648698773655)
            ·
              refine ⟨77864304224651473048160483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51909536149767648698773655 77864304224651473048160483)
              ·
                refine ⟨116796456336977209572240725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77864304224651473048160483 116796456336977209572240725)
                ·
                  refine ⟨171088559087368959334337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 116796456336977209572240725 171088559087368959334337)
                  ·
                    rfl

theorem cell23_2998744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_2998744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998744 prefixEnd_2998744 := by exact prefixLift 2998744
  have htrace : WordTrace (prefixWord ++ tailWord_2998744) baseStart_2998744 baseEnd_2998744 := by
    simpa [prefixWord, tailWord_2998744, baseEnd_2998744] using wordTrace_append hprefix tailTrace_2998744
  have hstable : (prefixWord ++ tailWord_2998744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998744).length < 2 ^ (prefixWord ++ tailWord_2998744).sum := by decide
  have hdescent : baseEnd_2998744 < baseStart_2998744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998751 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_2998751 : Nat := 118140960795 + 2998751 * 2 ^ 59
def prefixEnd_2998751 : Nat := 4983230072969 + 3 ^ 40 * 2998751 * 2
def baseEnd_2998751 : Nat := 1539800626150902106621501

theorem tailTrace_2998751 : CollatzResearch.WordTrace tailWord_2998751 prefixEnd_2998751 1539800626150902106621501 := by
  unfold tailWord_2998751
  simp only [CollatzResearch.WordTrace]
  refine ⟨109373434359044747741892107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72915622906029831827928071 109373434359044747741892107)
  ·
    refine ⟨164060151538567121612838161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109373434359044747741892107 164060151538567121612838161)
    ·
      refine ⟨123045113653925341209628621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164060151538567121612838161 123045113653925341209628621)
      ·
        refine ⟨46141917620222002953610733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123045113653925341209628621 46141917620222002953610733)
        ·
          refine ⟨17303219107583251107604025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46141917620222002953610733 17303219107583251107604025)
          ·
            refine ⟨12977414330687438330703019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17303219107583251107604025 12977414330687438330703019)
            ·
              refine ⟨19466121496031157496054529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12977414330687438330703019 19466121496031157496054529)
              ·
                refine ⟨14599591122023368122040897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19466121496031157496054529 14599591122023368122040897)
                ·
                  refine ⟨10949693341517526091530673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14599591122023368122040897 10949693341517526091530673)
                  ·
                    refine ⟨8212270006138144568648005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10949693341517526091530673 8212270006138144568648005)
                    ·
                      refine ⟨1539800626150902106621501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8212270006138144568648005 1539800626150902106621501)
                      ·
                        rfl

theorem cell23_2998751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_2998751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998751 prefixEnd_2998751 := by exact prefixLift 2998751
  have htrace : WordTrace (prefixWord ++ tailWord_2998751) baseStart_2998751 baseEnd_2998751 := by
    simpa [prefixWord, tailWord_2998751, baseEnd_2998751] using wordTrace_append hprefix tailTrace_2998751
  have hstable : (prefixWord ++ tailWord_2998751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998751).length < 2 ^ (prefixWord ++ tailWord_2998751).sum := by decide
  have hdescent : baseEnd_2998751 < baseStart_2998751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998771 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3]
def baseStart_2998771 : Nat := 118140960795 + 2998771 * 2 ^ 59
def prefixEnd_2998771 : Nat := 4983230072969 + 3 ^ 40 * 2998771 * 2
def baseEnd_2998771 : Nat := 1539810895763992028371409

theorem tailTrace_2998771 : CollatzResearch.WordTrace tailWord_2998771 prefixEnd_2998771 1539810895763992028371409 := by
  unfold tailWord_2998771
  simp only [CollatzResearch.WordTrace]
  refine ⟨109374163818972291157620167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72916109212648194105080111 109374163818972291157620167)
  ·
    refine ⟨164061245728458436736430251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109374163818972291157620167 164061245728458436736430251)
    ·
      refine ⟨246091868592687655104645377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164061245728458436736430251 246091868592687655104645377)
      ·
        refine ⟨184568901444515741328484033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246091868592687655104645377 184568901444515741328484033)
        ·
          refine ⟨138426676083386805996363025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184568901444515741328484033 138426676083386805996363025)
          ·
            refine ⟨103820007062540104497272269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138426676083386805996363025 103820007062540104497272269)
            ·
              refine ⟨38932502648452539186477101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103820007062540104497272269 38932502648452539186477101)
              ·
                refine ⟨14599688493169702194928913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38932502648452539186477101 14599688493169702194928913)
                ·
                  refine ⟨10949766369877276646196685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14599688493169702194928913 10949766369877276646196685)
                  ·
                    refine ⟨4106162388703978742323757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10949766369877276646196685 4106162388703978742323757)
                    ·
                      refine ⟨1539810895763992028371409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106162388703978742323757 1539810895763992028371409)
                      ·
                        rfl

theorem cell23_2998771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_2998771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998771 prefixEnd_2998771 := by exact prefixLift 2998771
  have htrace : WordTrace (prefixWord ++ tailWord_2998771) baseStart_2998771 baseEnd_2998771 := by
    simpa [prefixWord, tailWord_2998771, baseEnd_2998771] using wordTrace_append hprefix tailTrace_2998771
  have hstable : (prefixWord ++ tailWord_2998771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998771).length < 2 ^ (prefixWord ++ tailWord_2998771).sum := by decide
  have hdescent : baseEnd_2998771 < baseStart_2998771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998795 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 5]
def baseStart_2998795 : Nat := 118140960795 + 2998795 * 2 ^ 59
def prefixEnd_2998795 : Nat := 4983230072969 + 3 ^ 40 * 2998795 * 2
def baseEnd_2998795 : Nat := 171091468811077770496811

theorem tailTrace_2998795 : CollatzResearch.WordTrace tailWord_2998795 prefixEnd_2998795 171091468811077770496811 := by
  unfold tailWord_2998795
  simp only [CollatzResearch.WordTrace]
  refine ⟨109375039170885343256493839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72916692780590228837662559 109375039170885343256493839)
  ·
    refine ⟨164062558756328014884740759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109375039170885343256493839 164062558756328014884740759)
    ·
      refine ⟨246093838134492022327111139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164062558756328014884740759 246093838134492022327111139)
      ·
        refine ⟨369140757201738033490666709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246093838134492022327111139 369140757201738033490666709)
        ·
          refine ⟨8651736496915735159937501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 369140757201738033490666709 8651736496915735159937501)
          ·
            refine ⟨3244401186343400684976563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8651736496915735159937501 3244401186343400684976563)
            ·
              refine ⟨4866601779515101027464845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244401186343400684976563 4866601779515101027464845)
              ·
                refine ⟨1824975667318162885299317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866601779515101027464845 1824975667318162885299317)
                ·
                  refine ⟨171091468811077770496811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824975667318162885299317 171091468811077770496811)
                  ·
                    rfl

theorem cell23_2998795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 5].length) (baseStart_2998795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998795 prefixEnd_2998795 := by exact prefixLift 2998795
  have htrace : WordTrace (prefixWord ++ tailWord_2998795) baseStart_2998795 baseEnd_2998795 := by
    simpa [prefixWord, tailWord_2998795, baseEnd_2998795] using wordTrace_append hprefix tailTrace_2998795
  have hstable : (prefixWord ++ tailWord_2998795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998795).length < 2 ^ (prefixWord ++ tailWord_2998795).sum := by decide
  have hdescent : baseEnd_2998795 < baseStart_2998795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998808 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_2998808 : Nat := 118140960795 + 2998808 * 2 ^ 59
def prefixEnd_2998808 : Nat := 4983230072969 + 3 ^ 40 * 2998808 * 2
def baseEnd_2998808 : Nat := 513276631516069461202913

theorem tailTrace_2998808 : CollatzResearch.WordTrace tailWord_2998808 prefixEnd_2998808 513276631516069461202913 := by
  unfold tailWord_2998808
  simp only [CollatzResearch.WordTrace]
  refine ⟨54687756659919123238358539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72917008879892164317811385 54687756659919123238358539)
  ·
    refine ⟨82031634989878684857537809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54687756659919123238358539 82031634989878684857537809)
    ·
      refine ⟨61523726242409013643153357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82031634989878684857537809 61523726242409013643153357)
      ·
        refine ⟨23071397340903380116182509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61523726242409013643153357 23071397340903380116182509)
        ·
          refine ⟨8651774002838767543568441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23071397340903380116182509 8651774002838767543568441)
          ·
            refine ⟨6488830502129075657676331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651774002838767543568441 6488830502129075657676331)
            ·
              refine ⟨9733245753193613486514497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488830502129075657676331 9733245753193613486514497)
              ·
                refine ⟨7299934314895210114885873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9733245753193613486514497 7299934314895210114885873)
                ·
                  refine ⟨5474950736171407586164405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7299934314895210114885873 5474950736171407586164405)
                  ·
                    refine ⟨513276631516069461202913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5474950736171407586164405 513276631516069461202913)
                    ·
                      rfl

theorem cell23_2998808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_2998808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998808 prefixEnd_2998808 := by exact prefixLift 2998808
  have htrace : WordTrace (prefixWord ++ tailWord_2998808) baseStart_2998808 baseEnd_2998808 := by
    simpa [prefixWord, tailWord_2998808, baseEnd_2998808] using wordTrace_append hprefix tailTrace_2998808
  have hstable : (prefixWord ++ tailWord_2998808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998808).length < 2 ^ (prefixWord ++ tailWord_2998808).sum := by decide
  have hdescent : baseEnd_2998808 < baseStart_2998808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998823 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2998823 : Nat := 118140960795 + 2998823 * 2 ^ 59
def prefixEnd_2998823 : Nat := 4983230072969 + 3 ^ 40 * 2998823 * 2
def baseEnd_2998823 : Nat := 1539837596758025824921171

theorem tailTrace_2998823 : CollatzResearch.WordTrace tailWord_2998823 prefixEnd_2998823 1539837596758025824921171 := by
  unfold tailWord_2998823
  simp only [CollatzResearch.WordTrace]
  refine ⟨109376060414783904038513123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72917373609855936025675415 109376060414783904038513123)
  ·
    refine ⟨164064090622175856057769685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109376060414783904038513123 164064090622175856057769685)
    ·
      refine ⟨3845252123957246626353977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 164064090622175856057769685 3845252123957246626353977)
      ·
        refine ⟨2883939092967934969765483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845252123957246626353977 2883939092967934969765483)
        ·
          refine ⟨4325908639451902454648225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883939092967934969765483 4325908639451902454648225)
          ·
            refine ⟨3244431479588926840986169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325908639451902454648225 3244431479588926840986169)
            ·
              refine ⟨2433323609691695130739627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244431479588926840986169 2433323609691695130739627)
              ·
                refine ⟨3649985414537542696109441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433323609691695130739627 3649985414537542696109441)
                ·
                  refine ⟨2737489060903157022082081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3649985414537542696109441 2737489060903157022082081)
                  ·
                    refine ⟨2053116795677367766561561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2737489060903157022082081 2053116795677367766561561)
                    ·
                      refine ⟨1539837596758025824921171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053116795677367766561561 1539837596758025824921171)
                      ·
                        rfl

theorem cell23_2998823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2998823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998823 prefixEnd_2998823 := by exact prefixLift 2998823
  have htrace : WordTrace (prefixWord ++ tailWord_2998823) baseStart_2998823 baseEnd_2998823 := by
    simpa [prefixWord, tailWord_2998823, baseEnd_2998823] using wordTrace_append hprefix tailTrace_2998823
  have hstable : (prefixWord ++ tailWord_2998823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998823).length < 2 ^ (prefixWord ++ tailWord_2998823).sum := by decide
  have hdescent : baseEnd_2998823 < baseStart_2998823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998828 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 2, 4, 2]
def baseStart_2998828 : Nat := 118140960795 + 2998828 * 2 ^ 59
def prefixEnd_2998828 : Nat := 4983230072969 + 3 ^ 40 * 2998828 * 2
def baseEnd_2998828 : Nat := 1539840164161298305358647

theorem tailTrace_2998828 : CollatzResearch.WordTrace tailWord_2998828 prefixEnd_2998828 1539840164161298305358647 := by
  unfold tailWord_2998828
  simp only [CollatzResearch.WordTrace]
  refine ⟨54688121389882894946222569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72917495186510526594963425 54688121389882894946222569)
  ·
    refine ⟨41016091042412171209666927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54688121389882894946222569 41016091042412171209666927)
    ·
      refine ⟨61524136563618256814500391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41016091042412171209666927 61524136563618256814500391)
      ·
        refine ⟨92286204845427385221750587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61524136563618256814500391 92286204845427385221750587)
        ·
          refine ⟨138429307268141077832625881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92286204845427385221750587 138429307268141077832625881)
          ·
            refine ⟨103821980451105808374469411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138429307268141077832625881 103821980451105808374469411)
            ·
              refine ⟨155732970676658712561704117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103821980451105808374469411 155732970676658712561704117)
              ·
                refine ⟨14599966000936754302659761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155732970676658712561704117 14599966000936754302659761)
                ·
                  refine ⟨10949974500702565726994821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14599966000936754302659761 10949974500702565726994821)
                  ·
                    refine ⟨2053120218881731073811529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10949974500702565726994821 2053120218881731073811529)
                    ·
                      refine ⟨1539840164161298305358647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053120218881731073811529 1539840164161298305358647)
                      ·
                        rfl

theorem cell23_2998828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_2998828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998828 prefixEnd_2998828 := by exact prefixLift 2998828
  have htrace : WordTrace (prefixWord ++ tailWord_2998828) baseStart_2998828 baseEnd_2998828 := by
    simpa [prefixWord, tailWord_2998828, baseEnd_2998828] using wordTrace_append hprefix tailTrace_2998828
  have hstable : (prefixWord ++ tailWord_2998828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998828).length < 2 ^ (prefixWord ++ tailWord_2998828).sum := by decide
  have hdescent : baseEnd_2998828 < baseStart_2998828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998845 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2998845 : Nat := 118140960795 + 2998845 * 2 ^ 59
def prefixEnd_2998845 : Nat := 4983230072969 + 3 ^ 40 * 2998845 * 2
def baseEnd_2998845 : Nat := 1539848893332424738846069

theorem tailTrace_2998845 : CollatzResearch.WordTrace tailWord_2998845 prefixEnd_2998845 1539848893332424738846069 := by
  unfold tailWord_2998845
  simp only [CollatzResearch.WordTrace]
  refine ⟨109376862820704201795813989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72917908547136134530542659 109376862820704201795813989)
  ·
    refine ⟨20508161778882037836715123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109376862820704201795813989 20508161778882037836715123)
    ·
      refine ⟨30762242668323056755072685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20508161778882037836715123 30762242668323056755072685)
      ·
        refine ⟨11535841000621146283152257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30762242668323056755072685 11535841000621146283152257)
        ·
          refine ⟨8651880750465859712364193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11535841000621146283152257 8651880750465859712364193)
          ·
            refine ⟨6488910562849394784273145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651880750465859712364193 6488910562849394784273145)
            ·
              refine ⟨4866682922137046088204859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6488910562849394784273145 4866682922137046088204859)
              ·
                refine ⟨7300024383205569132307289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866682922137046088204859 7300024383205569132307289)
                ·
                  refine ⟨5475018287404176849230467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7300024383205569132307289 5475018287404176849230467)
                  ·
                    refine ⟨8212527431106265273845701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5475018287404176849230467 8212527431106265273845701)
                    ·
                      refine ⟨1539848893332424738846069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8212527431106265273845701 1539848893332424738846069)
                      ·
                        rfl

theorem cell23_2998845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2998845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998845 prefixEnd_2998845 := by exact prefixLift 2998845
  have htrace : WordTrace (prefixWord ++ tailWord_2998845) baseStart_2998845 baseEnd_2998845 := by
    simpa [prefixWord, tailWord_2998845, baseEnd_2998845] using wordTrace_append hprefix tailTrace_2998845
  have hstable : (prefixWord ++ tailWord_2998845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998845).length < 2 ^ (prefixWord ++ tailWord_2998845).sum := by decide
  have hdescent : baseEnd_2998845 < baseStart_2998845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998848 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_2998848 : Nat := 118140960795 + 2998848 * 2 ^ 59
def prefixEnd_2998848 : Nat := 4983230072969 + 3 ^ 40 * 2998848 * 2
def baseEnd_2998848 : Nat := 1539850433774388227108555

theorem tailTrace_2998848 : CollatzResearch.WordTrace tailWord_2998848 prefixEnd_2998848 1539850433774388227108555 := by
  unfold tailWord_2998848
  simp only [CollatzResearch.WordTrace]
  refine ⟨54688486119846666654086599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72917981493128888872115465 54688486119846666654086599)
  ·
    refine ⟨82032729179769999981129899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54688486119846666654086599 82032729179769999981129899)
    ·
      refine ⟨123049093769654999971694849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82032729179769999981129899 123049093769654999971694849)
      ·
        refine ⟨92286820327241249978771137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123049093769654999971694849 92286820327241249978771137)
        ·
          refine ⟨69215115245430937484078353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92286820327241249978771137 69215115245430937484078353)
          ·
            refine ⟨51911336434073203113058765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69215115245430937484078353 51911336434073203113058765)
            ·
              refine ⟨19466751162777451167397037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51911336434073203113058765 19466751162777451167397037)
              ·
                refine ⟨7300031686041544187773889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19466751162777451167397037 7300031686041544187773889)
                ·
                  refine ⟨5475023764531158140830417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7300031686041544187773889 5475023764531158140830417)
                  ·
                    refine ⟨4106267823398368605622813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5475023764531158140830417 4106267823398368605622813)
                    ·
                      refine ⟨1539850433774388227108555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106267823398368605622813 1539850433774388227108555)
                      ·
                        rfl

theorem cell23_2998848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_2998848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998848 prefixEnd_2998848 := by exact prefixLift 2998848
  have htrace : WordTrace (prefixWord ++ tailWord_2998848) baseStart_2998848 baseEnd_2998848 := by
    simpa [prefixWord, tailWord_2998848, baseEnd_2998848] using wordTrace_append hprefix tailTrace_2998848
  have hstable : (prefixWord ++ tailWord_2998848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998848).length < 2 ^ (prefixWord ++ tailWord_2998848).sum := by decide
  have hdescent : baseEnd_2998848 < baseStart_2998848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998868 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2998868 : Nat := 118140960795 + 2998868 * 2 ^ 59
def prefixEnd_2998868 : Nat := 4983230072969 + 3 ^ 40 * 2998868 * 2
def baseEnd_2998868 : Nat := 171095633709719794317607

theorem tailTrace_2998868 : CollatzResearch.WordTrace tailWord_2998868 prefixEnd_2998868 171095633709719794317607 := by
  unfold tailWord_2998868
  simp only [CollatzResearch.WordTrace]
  refine ⟨54688850849810438361950629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72918467799747251149267505 54688850849810438361950629)
  ·
    refine ⟨10254159534339457192865743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54688850849810438361950629 10254159534339457192865743)
    ·
      refine ⟨15381239301509185789298615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254159534339457192865743 15381239301509185789298615)
      ·
        refine ⟨23071858952263778683947923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15381239301509185789298615 23071858952263778683947923)
        ·
          refine ⟨34607788428395668025921885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23071858952263778683947923 34607788428395668025921885)
          ·
            refine ⟨12977920660648375509720707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34607788428395668025921885 12977920660648375509720707)
            ·
              refine ⟨19466880990972563264581061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12977920660648375509720707 19466880990972563264581061)
              ·
                refine ⟨3650040185807355612108949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19466880990972563264581061 3650040185807355612108949)
                ·
                  refine ⟨171095633709719794317607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3650040185807355612108949 171095633709719794317607)
                  ·
                    rfl

theorem cell23_2998868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2998868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998868 prefixEnd_2998868 := by exact prefixLift 2998868
  have htrace : WordTrace (prefixWord ++ tailWord_2998868) baseStart_2998868 baseEnd_2998868 := by
    simpa [prefixWord, tailWord_2998868, baseEnd_2998868] using wordTrace_append hprefix tailTrace_2998868
  have hstable : (prefixWord ++ tailWord_2998868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998868).length < 2 ^ (prefixWord ++ tailWord_2998868).sum := by decide
  have hdescent : baseEnd_2998868 < baseStart_2998868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998871 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2998871 : Nat := 118140960795 + 2998871 * 2 ^ 59
def prefixEnd_2998871 : Nat := 4983230072969 + 3 ^ 40 * 2998871 * 2
def baseEnd_2998871 : Nat := 1539862243829441637120949

theorem tailTrace_2998871 : CollatzResearch.WordTrace tailWord_2998871 prefixEnd_2998871 1539862243829441637120949 := by
  unfold tailWord_2998871
  simp only [CollatzResearch.WordTrace]
  refine ⟨109377811118610008236260467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72918540745740005490840311 109377811118610008236260467)
  ·
    refine ⟨164066716677915012354390701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109377811118610008236260467 164066716677915012354390701)
    ·
      refine ⟨61525018754218129632896513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164066716677915012354390701 61525018754218129632896513)
      ·
        refine ⟨46143764065663597224672385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61525018754218129632896513 46143764065663597224672385)
        ·
          refine ⟨34607823049247697918504289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46143764065663597224672385 34607823049247697918504289)
          ·
            refine ⟨25955867286935773438878217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34607823049247697918504289 25955867286935773438878217)
            ·
              refine ⟨19466900465201830079158663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25955867286935773438878217 19466900465201830079158663)
              ·
                refine ⟨29200350697802745118737995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19466900465201830079158663 29200350697802745118737995)
                ·
                  refine ⟨43800526046704117678106993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29200350697802745118737995 43800526046704117678106993)
                  ·
                    refine ⟨32850394535028088258580245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43800526046704117678106993 32850394535028088258580245)
                    ·
                      refine ⟨1539862243829441637120949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32850394535028088258580245 1539862243829441637120949)
                      ·
                        rfl

theorem cell23_2998871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2998871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998871 prefixEnd_2998871 := by exact prefixLift 2998871
  have htrace : WordTrace (prefixWord ++ tailWord_2998871) baseStart_2998871 baseEnd_2998871 := by
    simpa [prefixWord, tailWord_2998871, baseEnd_2998871] using wordTrace_append hprefix tailTrace_2998871
  have hstable : (prefixWord ++ tailWord_2998871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998871).length < 2 ^ (prefixWord ++ tailWord_2998871).sum := by decide
  have hdescent : baseEnd_2998871 < baseStart_2998871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998872 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 1, 4]
def baseStart_2998872 : Nat := 118140960795 + 2998872 * 2 ^ 59
def prefixEnd_2998872 : Nat := 4983230072969 + 3 ^ 40 * 2998872 * 2
def baseEnd_2998872 : Nat := 513287585770032044402815

theorem tailTrace_2998872 : CollatzResearch.WordTrace tailWord_2998872 prefixEnd_2998872 513287585770032044402815 := by
  unfold tailWord_2998872
  simp only [CollatzResearch.WordTrace]
  refine ⟨54688923795803192703523435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72918565061070923604697913 54688923795803192703523435)
  ·
    refine ⟨82033385693704789055285153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54688923795803192703523435 82033385693704789055285153)
    ·
      refine ⟨61525039270278591791463865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82033385693704789055285153 61525039270278591791463865)
      ·
        refine ⟨46143779452708943843597899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61525039270278591791463865 46143779452708943843597899)
        ·
          refine ⟨69215669179063415765396849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46143779452708943843597899 69215669179063415765396849)
          ·
            refine ⟨51911751884297561824047637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69215669179063415765396849 51911751884297561824047637)
            ·
              refine ⟨2433363369576448210502233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51911751884297561824047637 2433363369576448210502233)
              ·
                refine ⟨1825022527182336157876675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433363369576448210502233 1825022527182336157876675)
                ·
                  refine ⟨2737533790773504236815013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825022527182336157876675 2737533790773504236815013)
                  ·
                    refine ⟨513287585770032044402815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2737533790773504236815013 513287585770032044402815)
                    ·
                      rfl

theorem cell23_2998872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_2998872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998872 prefixEnd_2998872 := by exact prefixLift 2998872
  have htrace : WordTrace (prefixWord ++ tailWord_2998872) baseStart_2998872 baseEnd_2998872 := by
    simpa [prefixWord, tailWord_2998872, baseEnd_2998872] using wordTrace_append hprefix tailTrace_2998872
  have hstable : (prefixWord ++ tailWord_2998872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998872).length < 2 ^ (prefixWord ++ tailWord_2998872).sum := by decide
  have hdescent : baseEnd_2998872 < baseStart_2998872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998905 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 1, 5, 2]
def baseStart_2998905 : Nat := 118140960795 + 2998905 * 2 ^ 59
def prefixEnd_2998905 : Nat := 4983230072969 + 3 ^ 40 * 2998905 * 2
def baseEnd_2998905 : Nat := 1539879702171694504095793

theorem tailTrace_2998905 : CollatzResearch.WordTrace tailWord_2998905 prefixEnd_2998905 1539879702171694504095793 := by
  unfold tailWord_2998905
  simp only [CollatzResearch.WordTrace]
  refine ⟨109379051200486832042998169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72919367466991221361998779 109379051200486832042998169)
  ·
    refine ⟨82034288400365124032248627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109379051200486832042998169 82034288400365124032248627)
    ·
      refine ⟨123051432600547686048372941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82034288400365124032248627 123051432600547686048372941)
      ·
        refine ⟨46144287225205382268139853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123051432600547686048372941 46144287225205382268139853)
        ·
          refine ⟨17304107709452018350552445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46144287225205382268139853 17304107709452018350552445)
          ·
            refine ⟨6489040391044506881457167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17304107709452018350552445 6489040391044506881457167)
            ·
              refine ⟨9733560586566760322185751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489040391044506881457167 9733560586566760322185751)
              ·
                refine ⟨14600340879850140483278627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733560586566760322185751 14600340879850140483278627)
                ·
                  refine ⟨21900511319775210724917941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14600340879850140483278627 21900511319775210724917941)
                  ·
                    refine ⟨2053172936228926005461057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21900511319775210724917941 2053172936228926005461057)
                    ·
                      refine ⟨1539879702171694504095793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053172936228926005461057 1539879702171694504095793)
                      ·
                        rfl

theorem cell23_2998905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_2998905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998905 prefixEnd_2998905 := by exact prefixLift 2998905
  have htrace : WordTrace (prefixWord ++ tailWord_2998905) baseStart_2998905 baseEnd_2998905 := by
    simpa [prefixWord, tailWord_2998905, baseEnd_2998905] using wordTrace_append hprefix tailTrace_2998905
  have hstable : (prefixWord ++ tailWord_2998905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998905).length < 2 ^ (prefixWord ++ tailWord_2998905).sum := by decide
  have hdescent : baseEnd_2998905 < baseStart_2998905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998911 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 3, 6]
def baseStart_2998911 : Nat := 118140960795 + 2998911 * 2 ^ 59
def prefixEnd_2998911 : Nat := 4983230072969 + 3 ^ 40 * 2998911 * 2
def baseEnd_2998911 : Nat := 513294261018540493540255

theorem tailTrace_2998911 : CollatzResearch.WordTrace tailWord_2998911 prefixEnd_2998911 513294261018540493540255 := by
  unfold tailWord_2998911
  simp only [CollatzResearch.WordTrace]
  refine ⟨109379270038465095067716587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72919513358976730045144391 109379270038465095067716587)
  ·
    refine ⟨164068905057697642601574881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109379270038465095067716587 164068905057697642601574881)
    ·
      refine ⟨123051678793273231951181161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164068905057697642601574881 123051678793273231951181161)
      ·
        refine ⟨92288759094954923963385871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123051678793273231951181161 92288759094954923963385871)
        ·
          refine ⟨138433138642432385945078807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92288759094954923963385871 138433138642432385945078807)
          ·
            refine ⟨207649707963648578917618211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138433138642432385945078807 207649707963648578917618211)
            ·
              refine ⟨311474561945472868376427317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207649707963648578917618211 311474561945472868376427317)
              ·
                refine ⟨29200740182388081410290061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311474561945472868376427317 29200740182388081410290061)
                ·
                  refine ⟨10950277568395530528858773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29200740182388081410290061 10950277568395530528858773)
                  ·
                    refine ⟨513294261018540493540255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10950277568395530528858773 513294261018540493540255)
                    ·
                      rfl

theorem cell23_2998911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_2998911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998911 prefixEnd_2998911 := by exact prefixLift 2998911
  have htrace : WordTrace (prefixWord ++ tailWord_2998911) baseStart_2998911 baseEnd_2998911 := by
    simpa [prefixWord, tailWord_2998911, baseEnd_2998911] using wordTrace_append hprefix tailTrace_2998911
  have hstable : (prefixWord ++ tailWord_2998911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998911).length < 2 ^ (prefixWord ++ tailWord_2998911).sum := by decide
  have hdescent : baseEnd_2998911 < baseStart_2998911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998912 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 1, 1, 3]
def baseStart_2998912 : Nat := 118140960795 + 2998912 * 2 ^ 59
def prefixEnd_2998912 : Nat := 4983230072969 + 3 ^ 40 * 2998912 * 2
def baseEnd_2998912 : Nat := 1539883296536275976708261

theorem tailTrace_2998912 : CollatzResearch.WordTrace tailWord_2998912 prefixEnd_2998912 1539883296536275976708261 := by
  unfold tailWord_2998912
  simp only [CollatzResearch.WordTrace]
  refine ⟨54689653255730736119251495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72919537674307648159001993 54689653255730736119251495)
  ·
    refine ⟨82034479883596104178877243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54689653255730736119251495 82034479883596104178877243)
    ·
      refine ⟨123051719825394156268315865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82034479883596104178877243 123051719825394156268315865)
      ·
        refine ⟨92288789869045617201236899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123051719825394156268315865 92288789869045617201236899)
        ·
          refine ⟨138433184803568425801855349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92288789869045617201236899 138433184803568425801855349)
          ·
            refine ⟨12978111075334539918923939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138433184803568425801855349 12978111075334539918923939)
            ·
              refine ⟨19467166613001809878385909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12978111075334539918923939 19467166613001809878385909)
              ·
                refine ⟨1825046869968919676098679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19467166613001809878385909 1825046869968919676098679)
                ·
                  refine ⟨2737570304953379514148019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825046869968919676098679 2737570304953379514148019)
                  ·
                    refine ⟨4106355457430069271222029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2737570304953379514148019 4106355457430069271222029)
                    ·
                      refine ⟨1539883296536275976708261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106355457430069271222029 1539883296536275976708261)
                      ·
                        rfl

theorem cell23_2998912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_2998912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998912 prefixEnd_2998912 := by exact prefixLift 2998912
  have htrace : WordTrace (prefixWord ++ tailWord_2998912) baseStart_2998912 baseEnd_2998912 := by
    simpa [prefixWord, tailWord_2998912, baseEnd_2998912] using wordTrace_append hprefix tailTrace_2998912
  have hstable : (prefixWord ++ tailWord_2998912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998912).length < 2 ^ (prefixWord ++ tailWord_2998912).sum := by decide
  have hdescent : baseEnd_2998912 < baseStart_2998912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998915 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 1, 5]
def baseStart_2998915 : Nat := 118140960795 + 2998915 * 2 ^ 59
def prefixEnd_2998915 : Nat := 4983230072969 + 3 ^ 40 * 2998915 * 2
def baseEnd_2998915 : Nat := 513294945659413154990249

theorem tailTrace_2998915 : CollatzResearch.WordTrace tailWord_2998915 prefixEnd_2998915 513294945659413154990249 := by
  unfold tailWord_2998915
  simp only [CollatzResearch.WordTrace]
  refine ⟨109379415930450603750862199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72919610620300402500574799 109379415930450603750862199)
  ·
    refine ⟨164069123895675905626293299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109379415930450603750862199 164069123895675905626293299)
    ·
      refine ⟨246103685843513858439439949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164069123895675905626293299 246103685843513858439439949)
      ·
        refine ⟨92288882191317696914789981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246103685843513858439439949 92288882191317696914789981)
        ·
          refine ⟨34608330821744136343046243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92288882191317696914789981 34608330821744136343046243)
          ·
            refine ⟨51912496232616204514569365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34608330821744136343046243 51912496232616204514569365)
            ·
              refine ⟨2433398260903884586620439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51912496232616204514569365 2433398260903884586620439)
              ·
                refine ⟨3650097391355826879930659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433398260903884586620439 3650097391355826879930659)
                ·
                  refine ⟨5475146087033740319895989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650097391355826879930659 5475146087033740319895989)
                  ·
                    refine ⟨513294945659413154990249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5475146087033740319895989 513294945659413154990249)
                    ·
                      rfl

theorem cell23_2998915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 5].length) (baseStart_2998915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998915 prefixEnd_2998915 := by exact prefixLift 2998915
  have htrace : WordTrace (prefixWord ++ tailWord_2998915) baseStart_2998915 baseEnd_2998915 := by
    simpa [prefixWord, tailWord_2998915, baseEnd_2998915] using wordTrace_append hprefix tailTrace_2998915
  have hstable : (prefixWord ++ tailWord_2998915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998915).length < 2 ^ (prefixWord ++ tailWord_2998915).sum := by decide
  have hdescent : baseEnd_2998915 < baseStart_2998915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
