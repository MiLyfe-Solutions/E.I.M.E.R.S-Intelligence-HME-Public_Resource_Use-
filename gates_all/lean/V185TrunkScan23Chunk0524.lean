import V185TrunkScan23Chunk0523

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3097616 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_3097616 : Nat := 118140960795 + 3097616 * 2 ^ 59
def prefixEnd_3097616 : Nat := 4983230072969 + 3 ^ 40 * 3097616 * 2
def baseEnd_3097616 : Nat := 530188630352552598951443

theorem tailTrace_3097616 : CollatzResearch.WordTrace tailWord_3097616 prefixEnd_3097616 530188630352552598951443 := by
  unfold tailWord_3097616
  simp only [CollatzResearch.WordTrace]
  refine ⟨56489668572936868769812351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75319558097249158359749801 56489668572936868769812351)
  ·
    refine ⟨84734502859405303154718527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56489668572936868769812351 84734502859405303154718527)
    ·
      refine ⟨127101754289107954732077791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84734502859405303154718527 127101754289107954732077791)
      ·
        refine ⟨190652631433661932098116687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127101754289107954732077791 190652631433661932098116687)
        ·
          refine ⟨285978947150492898147175031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190652631433661932098116687 285978947150492898147175031)
          ·
            refine ⟨428968420725739347220762547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285978947150492898147175031 428968420725739347220762547)
            ·
              refine ⟨643452631088609020831143821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428968420725739347220762547 643452631088609020831143821)
              ·
                refine ⟨241294736658228382811678933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 643452631088609020831143821 241294736658228382811678933)
                ·
                  refine ⟨5655345390427227722148725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241294736658228382811678933 5655345390427227722148725)
                  ·
                    refine ⟨530188630352552598951443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5655345390427227722148725 530188630352552598951443)
                    ·
                      rfl

theorem cell23_3097616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_3097616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097616 prefixEnd_3097616 := by exact prefixLift 3097616
  have htrace : WordTrace (prefixWord ++ tailWord_3097616) baseStart_3097616 baseEnd_3097616 := by
    simpa [prefixWord, tailWord_3097616, baseEnd_3097616] using wordTrace_append hprefix tailTrace_3097616
  have hstable : (prefixWord ++ tailWord_3097616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097616).length < 2 ^ (prefixWord ++ tailWord_3097616).sum := by decide
  have hdescent : baseEnd_3097616 < baseStart_3097616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097624 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 1, 4]
def baseStart_3097624 : Nat := 118140960795 + 3097624 * 2 ^ 59
def prefixEnd_3097624 : Nat := 4983230072969 + 3 ^ 40 * 3097624 * 2
def baseEnd_3097624 : Nat := 530189999634297921851431

theorem tailTrace_3097624 : CollatzResearch.WordTrace tailWord_3097624 prefixEnd_3097624 530189999634297921851431 := by
  unfold tailWord_3097624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56489814464922377452957963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75319752619896503270610617 56489814464922377452957963)
  ·
    refine ⟨84734721697383566179436945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56489814464922377452957963 84734721697383566179436945)
    ·
      refine ⟨63551041273037674634577709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84734721697383566179436945 63551041273037674634577709)
      ·
        refine ⟨23831640477389127987966641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63551041273037674634577709 23831640477389127987966641)
        ·
          refine ⟨17873730358041845990974981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23831640477389127987966641 17873730358041845990974981)
          ·
            refine ⟨3351324442132846123307809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17873730358041845990974981 3351324442132846123307809)
            ·
              refine ⟨2513493331599634592480857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3351324442132846123307809 2513493331599634592480857)
              ·
                refine ⟨1885119998699725944360643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513493331599634592480857 1885119998699725944360643)
                ·
                  refine ⟨2827679998049588916540965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885119998699725944360643 2827679998049588916540965)
                  ·
                    refine ⟨530189999634297921851431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827679998049588916540965 530189999634297921851431)
                    ·
                      rfl

theorem cell23_3097624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_3097624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097624 prefixEnd_3097624 := by exact prefixLift 3097624
  have htrace : WordTrace (prefixWord ++ tailWord_3097624) baseStart_3097624 baseEnd_3097624 := by
    simpa [prefixWord, tailWord_3097624, baseEnd_3097624] using wordTrace_append hprefix tailTrace_3097624
  have hstable : (prefixWord ++ tailWord_3097624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097624).length < 2 ^ (prefixWord ++ tailWord_3097624).sum := by decide
  have hdescent : baseEnd_3097624 < baseStart_3097624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097633 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_3097633 : Nat := 118140960795 + 3097633 * 2 ^ 59
def prefixEnd_3097633 : Nat := 4983230072969 + 3 ^ 40 * 3097633 * 2
def baseEnd_3097633 : Nat := 530191540076261410113917

theorem tailTrace_3097633 : CollatzResearch.WordTrace tailWord_3097633 prefixEnd_3097633 530191540076261410113917 := by
  unfold tailWord_3097633
  simp only [CollatzResearch.WordTrace]
  refine ⟨112979957186812149442993553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75319971457874766295329035 112979957186812149442993553)
  ·
    refine ⟨84734967890109112082245165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112979957186812149442993553 84734967890109112082245165)
    ·
      refine ⟨31775612958790917030841937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84734967890109112082245165 31775612958790917030841937)
      ·
        refine ⟨23831709719093187773131453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31775612958790917030841937 23831709719093187773131453)
        ·
          refine ⟨8936891144659945414924295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23831709719093187773131453 8936891144659945414924295)
          ·
            refine ⟨13405336716989918122386443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936891144659945414924295 13405336716989918122386443)
            ·
              refine ⟨20108005075484877183579665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13405336716989918122386443 20108005075484877183579665)
              ·
                refine ⟨15081003806613657887684749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20108005075484877183579665 15081003806613657887684749)
                ·
                  refine ⟨5655376427480121707881781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15081003806613657887684749 5655376427480121707881781)
                  ·
                    refine ⟨530191540076261410113917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5655376427480121707881781 530191540076261410113917)
                    ·
                      rfl

theorem cell23_3097633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_3097633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097633 prefixEnd_3097633 := by exact prefixLift 3097633
  have htrace : WordTrace (prefixWord ++ tailWord_3097633) baseStart_3097633 baseEnd_3097633 := by
    simpa [prefixWord, tailWord_3097633, baseEnd_3097633] using wordTrace_append hprefix tailTrace_3097633
  have hstable : (prefixWord ++ tailWord_3097633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097633).length < 2 ^ (prefixWord ++ tailWord_3097633).sum := by decide
  have hdescent : baseEnd_3097633 < baseStart_3097633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097657 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3097657 : Nat := 118140960795 + 3097657 * 2 ^ 59
def prefixEnd_3097657 : Nat := 4983230072969 + 3 ^ 40 * 3097657 * 2
def baseEnd_3097657 : Nat := 1590586943764492136441641

theorem tailTrace_3097657 : CollatzResearch.WordTrace tailWord_3097657 prefixEnd_3097657 1590586943764492136441641 := by
  unfold tailWord_3097657
  simp only [CollatzResearch.WordTrace]
  refine ⟨112980832538725201541867225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75320555025816801027911483 112980832538725201541867225)
  ·
    refine ⟨84735624404043901156400419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112980832538725201541867225 84735624404043901156400419)
    ·
      refine ⟨127103436606065851734600629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84735624404043901156400419 127103436606065851734600629)
      ·
        refine ⟨11915947181818673600118809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127103436606065851734600629 11915947181818673600118809)
        ·
          refine ⟨8936960386364005200089107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11915947181818673600118809 8936960386364005200089107)
          ·
            refine ⟨13405440579546007800133661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936960386364005200089107 13405440579546007800133661)
            ·
              refine ⟨5027040217329752925050123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13405440579546007800133661 5027040217329752925050123)
              ·
                refine ⟨7540560325994629387575185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027040217329752925050123 7540560325994629387575185)
                ·
                  refine ⟨5655420244495972040681389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7540560325994629387575185 5655420244495972040681389)
                  ·
                    refine ⟨2120782591685989515255521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5655420244495972040681389 2120782591685989515255521)
                    ·
                      refine ⟨1590586943764492136441641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120782591685989515255521 1590586943764492136441641)
                      ·
                        rfl

theorem cell23_3097657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3097657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097657 prefixEnd_3097657 := by exact prefixLift 3097657
  have htrace : WordTrace (prefixWord ++ tailWord_3097657) baseStart_3097657 baseEnd_3097657 := by
    simpa [prefixWord, tailWord_3097657, baseEnd_3097657] using wordTrace_append hprefix tailTrace_3097657
  have hstable : (prefixWord ++ tailWord_3097657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097657).length < 2 ^ (prefixWord ++ tailWord_3097657).sum := by decide
  have hdescent : baseEnd_3097657 < baseStart_3097657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097663 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 4, 4]
def baseStart_3097663 : Nat := 118140960795 + 3097663 * 2 ^ 59
def prefixEnd_3097663 : Nat := 4983230072969 + 3 ^ 40 * 3097663 * 2
def baseEnd_3097663 : Nat := 530196674882806370988871

theorem tailTrace_3097663 : CollatzResearch.WordTrace tailWord_3097663 prefixEnd_3097663 530196674882806370988871 := by
  unfold tailWord_3097663
  simp only [CollatzResearch.WordTrace]
  refine ⟨112981051376703464566585643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75320700917802309711057095 112981051376703464566585643)
  ·
    refine ⟨169471577065055196849878465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112981051376703464566585643 169471577065055196849878465)
    ·
      refine ⟨127103682798791397637408849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169471577065055196849878465 127103682798791397637408849)
      ·
        refine ⟨95327762099093548228056637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127103682798791397637408849 95327762099093548228056637)
        ·
          refine ⟨35747910787160080585521239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95327762099093548228056637 35747910787160080585521239)
          ·
            refine ⟨53621866180740120878281859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35747910787160080585521239 53621866180740120878281859)
            ·
              refine ⟨80432799271110181317422789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53621866180740120878281859 80432799271110181317422789)
              ·
                refine ⟨15081149863333158997016773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80432799271110181317422789 15081149863333158997016773)
                ·
                  refine ⟨2827715599374967311940645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15081149863333158997016773 2827715599374967311940645)
                  ·
                    refine ⟨530196674882806370988871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827715599374967311940645 530196674882806370988871)
                    ·
                      rfl

theorem cell23_3097663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_3097663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097663 prefixEnd_3097663 := by exact prefixLift 3097663
  have htrace : WordTrace (prefixWord ++ tailWord_3097663) baseStart_3097663 baseEnd_3097663 := by
    simpa [prefixWord, tailWord_3097663, baseEnd_3097663] using wordTrace_append hprefix tailTrace_3097663
  have hstable : (prefixWord ++ tailWord_3097663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097663).length < 2 ^ (prefixWord ++ tailWord_3097663).sum := by decide
  have hdescent : baseEnd_3097663 < baseStart_3097663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097673 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_3097673 : Nat := 118140960795 + 3097673 * 2 ^ 59
def prefixEnd_3097673 : Nat := 4983230072969 + 3 ^ 40 * 3097673 * 2
def baseEnd_3097673 : Nat := 1590595159454964073841567

theorem tailTrace_3097673 : CollatzResearch.WordTrace tailWord_3097673 prefixEnd_3097673 1590595159454964073841567 := by
  unfold tailWord_3097673
  simp only [CollatzResearch.WordTrace]
  refine ⟨112981416106667236274449673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75320944071111490849633115 112981416106667236274449673)
  ·
    refine ⟨84736062080000427205837255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112981416106667236274449673 84736062080000427205837255)
    ·
      refine ⟨127104093120000640808755883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84736062080000427205837255 127104093120000640808755883)
      ·
        refine ⟨190656139680000961213133825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127104093120000640808755883 190656139680000961213133825)
        ·
          refine ⟨142992104760000720909850369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190656139680000961213133825 142992104760000720909850369)
          ·
            refine ⟨107244078570000540682387777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142992104760000720909850369 107244078570000540682387777)
            ·
              refine ⟨80433058927500405511790833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107244078570000540682387777 80433058927500405511790833)
              ·
                refine ⟨60324794195625304133843125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80433058927500405511790833 60324794195625304133843125)
                ·
                  refine ⟨5655449455839872262547793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60324794195625304133843125 5655449455839872262547793)
                  ·
                    refine ⟨4241587091879904196910845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5655449455839872262547793 4241587091879904196910845)
                    ·
                      refine ⟨1590595159454964073841567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4241587091879904196910845 1590595159454964073841567)
                      ·
                        rfl

theorem cell23_3097673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_3097673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097673 prefixEnd_3097673 := by exact prefixLift 3097673
  have htrace : WordTrace (prefixWord ++ tailWord_3097673) baseStart_3097673 baseEnd_3097673 := by
    simpa [prefixWord, tailWord_3097673, baseEnd_3097673] using wordTrace_append hprefix tailTrace_3097673
  have hstable : (prefixWord ++ tailWord_3097673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097673).length < 2 ^ (prefixWord ++ tailWord_3097673).sum := by decide
  have hdescent : baseEnd_3097673 < baseStart_3097673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097704 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3097704 : Nat := 118140960795 + 3097704 * 2 ^ 59
def prefixEnd_3097704 : Nat := 4983230072969 + 3 ^ 40 * 3097704 * 2
def baseEnd_3097704 : Nat := 1590611077355253452553925

theorem tailTrace_3097704 : CollatzResearch.WordTrace tailWord_3097704 prefixEnd_3097704 1590611077355253452553925 := by
  unfold tailWord_3097704
  simp only [CollatzResearch.WordTrace]
  refine ⟨56491273384777464284414083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75321697846369952379218777 56491273384777464284414083)
  ·
    refine ⟨84736910077166196426621125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56491273384777464284414083 84736910077166196426621125)
    ·
      refine ⟨15888170639468661829991461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84736910077166196426621125 15888170639468661829991461)
      ·
        refine ⟨2979031994900374093123399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15888170639468661829991461 2979031994900374093123399)
        ·
          refine ⟨4468547992350561139685099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979031994900374093123399 4468547992350561139685099)
          ·
            refine ⟨6702821988525841709527649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468547992350561139685099 6702821988525841709527649)
            ·
              refine ⟨5027116491394381282145737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6702821988525841709527649 5027116491394381282145737)
              ·
                refine ⟨3770337368545785961609303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5027116491394381282145737 3770337368545785961609303)
                ·
                  refine ⟨5655506052818678942413955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770337368545785961609303 5655506052818678942413955)
                  ·
                    refine ⟨8483259079228018413620933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655506052818678942413955 8483259079228018413620933)
                    ·
                      refine ⟨1590611077355253452553925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8483259079228018413620933 1590611077355253452553925)
                      ·
                        rfl

theorem cell23_3097704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3097704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097704 prefixEnd_3097704 := by exact prefixLift 3097704
  have htrace : WordTrace (prefixWord ++ tailWord_3097704) baseStart_3097704 baseEnd_3097704 := by
    simpa [prefixWord, tailWord_3097704, baseEnd_3097704] using wordTrace_append hprefix tailTrace_3097704
  have hstable : (prefixWord ++ tailWord_3097704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097704).length < 2 ^ (prefixWord ++ tailWord_3097704).sum := by decide
  have hdescent : baseEnd_3097704 < baseStart_3097704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097710 : List Nat := [4, 1, 2, 2, 1, 2, 4, 7]
def baseStart_3097710 : Nat := 118140960795 + 3097710 * 2 ^ 59
def prefixEnd_3097710 : Nat := 4983230072969 + 3 ^ 40 * 3097710 * 2
def baseEnd_3097710 : Nat := 58911635490340015891811

theorem tailTrace_3097710 : CollatzResearch.WordTrace tailWord_3097710 prefixEnd_3097710 58911635490340015891811 := by
  unfold tailWord_3097710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14122845700941648949193323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75321843738355461062364389 14122845700941648949193323)
  ·
    refine ⟨21184268551412473423789985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14122845700941648949193323 21184268551412473423789985)
    ·
      refine ⟨15888201413559355067842489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21184268551412473423789985 15888201413559355067842489)
      ·
        refine ⟨11916151060169516300881867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15888201413559355067842489 11916151060169516300881867)
        ·
          refine ⟨17874226590254274451322801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11916151060169516300881867 17874226590254274451322801)
          ·
            refine ⟨13405669942690705838492101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17874226590254274451322801 13405669942690705838492101)
            ·
              refine ⟨2513563114254507344717269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13405669942690705838492101 2513563114254507344717269)
              ·
                refine ⟨58911635490340015891811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2513563114254507344717269 58911635490340015891811)
                ·
                  rfl

theorem cell23_3097710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_3097710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097710 prefixEnd_3097710 := by exact prefixLift 3097710
  have htrace : WordTrace (prefixWord ++ tailWord_3097710) baseStart_3097710 baseEnd_3097710 := by
    simpa [prefixWord, tailWord_3097710, baseEnd_3097710] using wordTrace_append hprefix tailTrace_3097710
  have hstable : (prefixWord ++ tailWord_3097710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097710).length < 2 ^ (prefixWord ++ tailWord_3097710).sum := by decide
  have hdescent : baseEnd_3097710 < baseStart_3097710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097720 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_3097720 : Nat := 118140960795 + 3097720 * 2 ^ 59
def prefixEnd_3097720 : Nat := 4983230072969 + 3 ^ 40 * 3097720 * 2
def baseEnd_3097720 : Nat := 1590619293045725389953851

theorem tailTrace_3097720 : CollatzResearch.WordTrace tailWord_3097720 prefixEnd_3097720 1590619293045725389953851 := by
  unfold tailWord_3097720
  simp only [CollatzResearch.WordTrace]
  refine ⟨56491565168748481650705307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75322086891664642200940409 56491565168748481650705307)
  ·
    refine ⟨84737347753122722476057961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56491565168748481650705307 84737347753122722476057961)
    ·
      refine ⟨63553010814842041857043471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84737347753122722476057961 63553010814842041857043471)
      ·
        refine ⟨95329516222263062785565207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63553010814842041857043471 95329516222263062785565207)
        ·
          refine ⟨142994274333394594178347811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95329516222263062785565207 142994274333394594178347811)
          ·
            refine ⟨214491411500091891267521717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142994274333394594178347811 214491411500091891267521717)
            ·
              refine ⟨20108569828133614806330161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214491411500091891267521717 20108569828133614806330161)
              ·
                refine ⟨15081427371100211104747621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20108569828133614806330161 15081427371100211104747621)
                ·
                  refine ⟨2827767632081289582140179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15081427371100211104747621 2827767632081289582140179)
                  ·
                    refine ⟨4241651448121934373210269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2827767632081289582140179 4241651448121934373210269)
                    ·
                      refine ⟨1590619293045725389953851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4241651448121934373210269 1590619293045725389953851)
                      ·
                        rfl

theorem cell23_3097720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_3097720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097720 prefixEnd_3097720 := by exact prefixLift 3097720
  have htrace : WordTrace (prefixWord ++ tailWord_3097720) baseStart_3097720 baseEnd_3097720 := by
    simpa [prefixWord, tailWord_3097720, baseEnd_3097720] using wordTrace_append hprefix tailTrace_3097720
  have hstable : (prefixWord ++ tailWord_3097720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097720).length < 2 ^ (prefixWord ++ tailWord_3097720).sum := by decide
  have hdescent : baseEnd_3097720 < baseStart_3097720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097754 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3097754 : Nat := 118140960795 + 3097754 * 2 ^ 59
def prefixEnd_3097754 : Nat := 4983230072969 + 3 ^ 40 * 3097754 * 2
def baseEnd_3097754 : Nat := 1590636751387978256928695

theorem tailTrace_3097754 : CollatzResearch.WordTrace tailWord_3097754 prefixEnd_3097754 1590636751387978256928695 := by
  unfold tailWord_3097754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28246092604843446777037079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75322913612915858072098877 28246092604843446777037079)
  ·
    refine ⟨42369138907265170165555619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28246092604843446777037079 42369138907265170165555619)
    ·
      refine ⟨63553708360897755248333429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42369138907265170165555619 63553708360897755248333429)
      ·
        refine ⟨5958160158834164554531259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63553708360897755248333429 5958160158834164554531259)
        ·
          refine ⟨8937240238251246831796889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958160158834164554531259 8937240238251246831796889)
          ·
            refine ⟨6702930178688435123847667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8937240238251246831796889 6702930178688435123847667)
            ·
              refine ⟨10054395268032652685771501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6702930178688435123847667 10054395268032652685771501)
              ·
                refine ⟨3770398225512244757164313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10054395268032652685771501 3770398225512244757164313)
                ·
                  refine ⟨2827798669134183567873235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3770398225512244757164313 2827798669134183567873235)
                  ·
                    refine ⟨4241698003701275351809853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2827798669134183567873235 4241698003701275351809853)
                    ·
                      refine ⟨1590636751387978256928695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4241698003701275351809853 1590636751387978256928695)
                      ·
                        rfl

theorem cell23_3097754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3097754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097754 prefixEnd_3097754 := by exact prefixLift 3097754
  have htrace : WordTrace (prefixWord ++ tailWord_3097754) baseStart_3097754 baseEnd_3097754 := by
    simpa [prefixWord, tailWord_3097754, baseEnd_3097754] using wordTrace_append hprefix tailTrace_3097754
  have hstable : (prefixWord ++ tailWord_3097754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097754).length < 2 ^ (prefixWord ++ tailWord_3097754).sum := by decide
  have hdescent : baseEnd_3097754 < baseStart_3097754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097764 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_3097764 : Nat := 118140960795 + 3097764 * 2 ^ 59
def prefixEnd_3097764 : Nat := 4983230072969 + 3 ^ 40 * 3097764 * 2
def baseEnd_3097764 : Nat := 1590641886194523217803649

theorem tailTrace_3097764 : CollatzResearch.WordTrace tailWord_3097764 prefixEnd_3097764 1590641886194523217803649 := by
  unfold tailWord_3097764
  simp only [CollatzResearch.WordTrace]
  refine ⟨56492367574668779408006173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75323156766225039210674897 56492367574668779408006173)
  ·
    refine ⟨21184637840500792278002315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56492367574668779408006173 21184637840500792278002315)
    ·
      refine ⟨31776956760751188417003473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21184637840500792278002315 31776956760751188417003473)
      ·
        refine ⟨23832717570563391312752605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31776956760751188417003473 23832717570563391312752605)
        ·
          refine ⟨8937269088961271742282227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23832717570563391312752605 8937269088961271742282227)
          ·
            refine ⟨13405903633441907613423341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937269088961271742282227 13405903633441907613423341)
            ·
              refine ⟨5027213862540715355033753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13405903633441907613423341 5027213862540715355033753)
              ·
                refine ⟨3770410396905536516275315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5027213862540715355033753 3770410396905536516275315)
                ·
                  refine ⟨5655615595358304774412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770410396905536516275315 5655615595358304774412973)
                  ·
                    refine ⟨2120855848259364290404865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5655615595358304774412973 2120855848259364290404865)
                    ·
                      refine ⟨1590641886194523217803649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120855848259364290404865 1590641886194523217803649)
                      ·
                        rfl

theorem cell23_3097764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_3097764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097764 prefixEnd_3097764 := by exact prefixLift 3097764
  have htrace : WordTrace (prefixWord ++ tailWord_3097764) baseStart_3097764 baseEnd_3097764 := by
    simpa [prefixWord, tailWord_3097764, baseEnd_3097764] using wordTrace_append hprefix tailTrace_3097764
  have hstable : (prefixWord ++ tailWord_3097764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097764).length < 2 ^ (prefixWord ++ tailWord_3097764).sum := by decide
  have hdescent : baseEnd_3097764 < baseStart_3097764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097777 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3097777 : Nat := 118140960795 + 3097777 * 2 ^ 59
def prefixEnd_3097777 : Nat := 4983230072969 + 3 ^ 40 * 3097777 * 2
def baseEnd_3097777 : Nat := 1590648561443031666941089

theorem tailTrace_3097777 : CollatzResearch.WordTrace tailWord_3097777 prefixEnd_3097777 1590648561443031666941089 := by
  unfold tailWord_3097777
  simp only [CollatzResearch.WordTrace]
  refine ⟨112985209298290462036235585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75323472865526974690823723 112985209298290462036235585)
  ·
    refine ⟨84738906973717846527176689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112985209298290462036235585 84738906973717846527176689)
    ·
      refine ⟨63554180230288384895382517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84738906973717846527176689 63554180230288384895382517)
      ·
        refine ⟨5958204396589536083942111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63554180230288384895382517 5958204396589536083942111)
        ·
          refine ⟨8937306594884304125913167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958204396589536083942111 8937306594884304125913167)
          ·
            refine ⟨13405959892326456188869751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937306594884304125913167 13405959892326456188869751)
            ·
              refine ⟨20108939838489684283304627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13405959892326456188869751 20108939838489684283304627)
              ·
                refine ⟨30163409757734526424956941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20108939838489684283304627 30163409757734526424956941)
                ·
                  refine ⟨11311278659150447409358853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30163409757734526424956941 11311278659150447409358853)
                  ·
                    refine ⟨2120864748590708889254785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11311278659150447409358853 2120864748590708889254785)
                    ·
                      refine ⟨1590648561443031666941089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120864748590708889254785 1590648561443031666941089)
                      ·
                        rfl

theorem cell23_3097777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3097777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097777 prefixEnd_3097777 := by exact prefixLift 3097777
  have htrace : WordTrace (prefixWord ++ tailWord_3097777) baseStart_3097777 baseEnd_3097777 := by
    simpa [prefixWord, tailWord_3097777, baseEnd_3097777] using wordTrace_append hprefix tailTrace_3097777
  have hstable : (prefixWord ++ tailWord_3097777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097777).length < 2 ^ (prefixWord ++ tailWord_3097777).sum := by decide
  have hdescent : baseEnd_3097777 < baseStart_3097777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097823 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3097823 : Nat := 118140960795 + 3097823 * 2 ^ 59
def prefixEnd_3097823 : Nat := 4983230072969 + 3 ^ 40 * 3097823 * 2
def baseEnd_3097823 : Nat := 1590672181553138486965877

theorem tailTrace_3097823 : CollatzResearch.WordTrace tailWord_3097823 prefixEnd_3097823 1590672181553138486965877 := by
  unfold tailWord_3097823
  simp only [CollatzResearch.WordTrace]
  refine ⟨112986887056123811892410123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75324591370749207928273415 112986887056123811892410123)
  ·
    refine ⟨169480330584185717838615185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112986887056123811892410123 169480330584185717838615185)
    ·
      refine ⟨127110247938139288378961389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169480330584185717838615185 127110247938139288378961389)
      ·
        refine ⟨47666342976802233142110521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127110247938139288378961389 47666342976802233142110521)
        ·
          refine ⟨35749757232601674856582891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47666342976802233142110521 35749757232601674856582891)
          ·
            refine ⟨53624635848902512284874337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35749757232601674856582891 53624635848902512284874337)
            ·
              refine ⟨40218476886676884213655753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53624635848902512284874337 40218476886676884213655753)
              ·
                refine ⟨30163857665007663160241815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40218476886676884213655753 30163857665007663160241815)
                ·
                  refine ⟨45245786497511494740362723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30163857665007663160241815 45245786497511494740362723)
                  ·
                    refine ⟨67868679746267242110544085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45245786497511494740362723 67868679746267242110544085)
                    ·
                      refine ⟨1590672181553138486965877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67868679746267242110544085 1590672181553138486965877)
                      ·
                        rfl

theorem cell23_3097823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3097823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097823 prefixEnd_3097823 := by exact prefixLift 3097823
  have htrace : WordTrace (prefixWord ++ tailWord_3097823) baseStart_3097823 baseEnd_3097823 := by
    simpa [prefixWord, tailWord_3097823, baseEnd_3097823] using wordTrace_append hprefix tailTrace_3097823
  have hstable : (prefixWord ++ tailWord_3097823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097823).length < 2 ^ (prefixWord ++ tailWord_3097823).sum := by decide
  have hdescent : baseEnd_3097823 < baseStart_3097823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097850 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_3097850 : Nat := 118140960795 + 3097850 * 2 ^ 59
def prefixEnd_3097850 : Nat := 4983230072969 + 3 ^ 40 * 3097850 * 2
def baseEnd_3097850 : Nat := 1590686045530809881328253

theorem tailTrace_3097850 : CollatzResearch.WordTrace tailWord_3097850 prefixEnd_3097850 1590686045530809881328253 := by
  unfold tailWord_3097850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28246967956756498875910751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75325247884683997002428669 28246967956756498875910751)
  ·
    refine ⟨42370451935134748313866127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28246967956756498875910751 42370451935134748313866127)
    ·
      refine ⟨63555677902702122470799191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42370451935134748313866127 63555677902702122470799191)
      ·
        refine ⟨95333516854053183706198787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63555677902702122470799191 95333516854053183706198787)
        ·
          refine ⟨143000275281079775559298181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95333516854053183706198787 143000275281079775559298181)
          ·
            refine ⟨26812551615202457917368409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143000275281079775559298181 26812551615202457917368409)
            ·
              refine ⟨20109413711401843438026307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26812551615202457917368409 20109413711401843438026307)
              ·
                refine ⟨30164120567102765157039461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20109413711401843438026307 30164120567102765157039461)
                ·
                  refine ⟨5655772606331768466944899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30164120567102765157039461 5655772606331768466944899)
                  ·
                    refine ⟨8483658909497652700417349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655772606331768466944899 8483658909497652700417349)
                    ·
                      refine ⟨1590686045530809881328253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8483658909497652700417349 1590686045530809881328253)
                      ·
                        rfl

theorem cell23_3097850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_3097850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097850 prefixEnd_3097850 := by exact prefixLift 3097850
  have htrace : WordTrace (prefixWord ++ tailWord_3097850) baseStart_3097850 baseEnd_3097850 := by
    simpa [prefixWord, tailWord_3097850, baseEnd_3097850] using wordTrace_append hprefix tailTrace_3097850
  have hstable : (prefixWord ++ tailWord_3097850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097850).length < 2 ^ (prefixWord ++ tailWord_3097850).sum := by decide
  have hdescent : baseEnd_3097850 < baseStart_3097850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097867 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 2, 4, 2]
def baseStart_3097867 : Nat := 118140960795 + 3097867 * 2 ^ 59
def prefixEnd_3097867 : Nat := 4983230072969 + 3 ^ 40 * 3097867 * 2
def baseEnd_3097867 : Nat := 1590694774701936314815675

theorem tailTrace_3097867 : CollatzResearch.WordTrace tailWord_3097867 prefixEnd_3097867 1590694774701936314815675 := by
  unfold tailWord_3097867
  simp only [CollatzResearch.WordTrace]
  refine ⟨112988491867964407407011855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75325661245309604938007903 112988491867964407407011855)
  ·
    refine ⟨169482737801946611110517783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112988491867964407407011855 169482737801946611110517783)
    ·
      refine ⟨254224106702919916665776675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169482737801946611110517783 254224106702919916665776675)
      ·
        refine ⟨381336160054379874998665013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254224106702919916665776675 381336160054379874998665013)
        ·
          refine ⟨35750265005098113281124845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 381336160054379874998665013 35750265005098113281124845)
          ·
            refine ⟨13406349376911792480421817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35750265005098113281124845 13406349376911792480421817)
            ·
              refine ⟨10054762032683844360316363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13406349376911792480421817 10054762032683844360316363)
              ·
                refine ⟨15082143049025766540474545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10054762032683844360316363 15082143049025766540474545)
                ·
                  refine ⟨11311607286769324905355909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15082143049025766540474545 11311607286769324905355909)
                  ·
                    refine ⟨2120926366269248419754233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11311607286769324905355909 2120926366269248419754233)
                    ·
                      refine ⟨1590694774701936314815675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120926366269248419754233 1590694774701936314815675)
                      ·
                        rfl

theorem cell23_3097867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4, 2].length) (baseStart_3097867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097867 prefixEnd_3097867 := by exact prefixLift 3097867
  have htrace : WordTrace (prefixWord ++ tailWord_3097867) baseStart_3097867 baseEnd_3097867 := by
    simpa [prefixWord, tailWord_3097867, baseEnd_3097867] using wordTrace_append hprefix tailTrace_3097867
  have hstable : (prefixWord ++ tailWord_3097867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097867).length < 2 ^ (prefixWord ++ tailWord_3097867).sum := by decide
  have hdescent : baseEnd_3097867 < baseStart_3097867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097920 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_3097920 : Nat := 118140960795 + 3097920 * 2 ^ 59
def prefixEnd_3097920 : Nat := 4983230072969 + 3 ^ 40 * 3097920 * 2
def baseEnd_3097920 : Nat := 530240663058874869150977

theorem tailTrace_3097920 : CollatzResearch.WordTrace tailWord_3097920 prefixEnd_3097920 530240663058874869150977 := by
  unfold tailWord_3097920
  simp only [CollatzResearch.WordTrace]
  refine ⟨56495212468386198729345607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75326949957848264972460809 56495212468386198729345607)
  ·
    refine ⟨84742818702579298094018411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56495212468386198729345607 84742818702579298094018411)
    ·
      refine ⟨127114228053868947141027617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84742818702579298094018411 127114228053868947141027617)
      ·
        refine ⟨95335671040401710355770713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127114228053868947141027617 95335671040401710355770713)
        ·
          refine ⟨71501753280301282766828035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95335671040401710355770713 71501753280301282766828035)
          ·
            refine ⟨107252629920451924150242053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71501753280301282766828035 107252629920451924150242053)
            ·
              refine ⟨20109868110084735778170385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107252629920451924150242053 20109868110084735778170385)
              ·
                refine ⟨15082401082563551833627789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20109868110084735778170385 15082401082563551833627789)
                ·
                  refine ⟨5655900405961331937610421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15082401082563551833627789 5655900405961331937610421)
                  ·
                    refine ⟨530240663058874869150977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5655900405961331937610421 530240663058874869150977)
                    ·
                      rfl

theorem cell23_3097920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_3097920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097920 prefixEnd_3097920 := by exact prefixLift 3097920
  have htrace : WordTrace (prefixWord ++ tailWord_3097920) baseStart_3097920 baseEnd_3097920 := by
    simpa [prefixWord, tailWord_3097920, baseEnd_3097920] using wordTrace_append hprefix tailTrace_3097920
  have hstable : (prefixWord ++ tailWord_3097920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097920).length < 2 ^ (prefixWord ++ tailWord_3097920).sum := by decide
  have hdescent : baseEnd_3097920 < baseStart_3097920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097924 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 6]
def baseStart_3097924 : Nat := 118140960795 + 3097924 * 2 ^ 59
def prefixEnd_3097924 : Nat := 4983230072969 + 3 ^ 40 * 3097924 * 2
def baseEnd_3097924 : Nat := 176747115899915843533657

theorem tailTrace_3097924 : CollatzResearch.WordTrace tailWord_3097924 prefixEnd_3097924 176747115899915843533657 := by
  unfold tailWord_3097924
  simp only [CollatzResearch.WordTrace]
  refine ⟨56495285414378953070918413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75327047219171937427891217 56495285414378953070918413)
  ·
    refine ⟨21185732030392107401594405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56495285414378953070918413 21185732030392107401594405)
    ·
      refine ⟨3972324755698520137798951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21185732030392107401594405 3972324755698520137798951)
      ·
        refine ⟨5958487133547780206698427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972324755698520137798951 5958487133547780206698427)
        ·
          refine ⟨8937730700321670310047641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958487133547780206698427 8937730700321670310047641)
          ·
            refine ⟨6703298025241252732535731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8937730700321670310047641 6703298025241252732535731)
            ·
              refine ⟨10054947037861879098803597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703298025241252732535731 10054947037861879098803597)
              ·
                refine ⟨3770605139198204662051349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10054947037861879098803597 3770605139198204662051349)
                ·
                  refine ⟨176747115899915843533657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3770605139198204662051349 176747115899915843533657)
                  ·
                    rfl

theorem cell23_3097924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_3097924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097924 prefixEnd_3097924 := by exact prefixLift 3097924
  have htrace : WordTrace (prefixWord ++ tailWord_3097924) baseStart_3097924 baseEnd_3097924 := by
    simpa [prefixWord, tailWord_3097924, baseEnd_3097924] using wordTrace_append hprefix tailTrace_3097924
  have hstable : (prefixWord ++ tailWord_3097924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097924).length < 2 ^ (prefixWord ++ tailWord_3097924).sum := by decide
  have hdescent : baseEnd_3097924 < baseStart_3097924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097944 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 2, 3, 2]
def baseStart_3097944 : Nat := 118140960795 + 3097944 * 2 ^ 59
def prefixEnd_3097944 : Nat := 4983230072969 + 3 ^ 40 * 3097944 * 2
def baseEnd_3097944 : Nat := 1590734312712332513552821

theorem tailTrace_3097944 : CollatzResearch.WordTrace tailWord_3097944 prefixEnd_3097944 1590734312712332513552821 := by
  unfold tailWord_3097944
  simp only [CollatzResearch.WordTrace]
  refine ⟨56495650144342724778782443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75327533525790299705043257 56495650144342724778782443)
  ·
    refine ⟨84743475216514087168173665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56495650144342724778782443 84743475216514087168173665)
    ·
      refine ⟨63557606412385565376130249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84743475216514087168173665 63557606412385565376130249)
      ·
        refine ⟨47668204809289174032097687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63557606412385565376130249 47668204809289174032097687)
        ·
          refine ⟨71502307213933761048146531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47668204809289174032097687 71502307213933761048146531)
          ·
            refine ⟨107253460820900641572219797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71502307213933761048146531 107253460820900641572219797)
            ·
              refine ⟨5027505975979717573697803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107253460820900641572219797 5027505975979717573697803)
              ·
                refine ⟨7541258963969576360546705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027505975979717573697803 7541258963969576360546705)
                ·
                  refine ⟨5655944222977182270410029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541258963969576360546705 5655944222977182270410029)
                  ·
                    refine ⟨2120979083616443351403761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5655944222977182270410029 2120979083616443351403761)
                    ·
                      refine ⟨1590734312712332513552821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2120979083616443351403761 1590734312712332513552821)
                      ·
                        rfl

theorem cell23_3097944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_3097944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097944 prefixEnd_3097944 := by exact prefixLift 3097944
  have htrace : WordTrace (prefixWord ++ tailWord_3097944) baseStart_3097944 baseEnd_3097944 := by
    simpa [prefixWord, tailWord_3097944, baseEnd_3097944] using wordTrace_append hprefix tailTrace_3097944
  have hstable : (prefixWord ++ tailWord_3097944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097944).length < 2 ^ (prefixWord ++ tailWord_3097944).sum := by decide
  have hdescent : baseEnd_3097944 < baseStart_3097944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097977 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_3097977 : Nat := 118140960795 + 3097977 * 2 ^ 59
def prefixEnd_3097977 : Nat := 4983230072969 + 3 ^ 40 * 3097977 * 2
def baseEnd_3097977 : Nat := 1590751257573930884440169

theorem tailTrace_3097977 : CollatzResearch.WordTrace tailWord_3097977 prefixEnd_3097977 1590751257573930884440169 := by
  unfold tailWord_3097977
  simp only [CollatzResearch.WordTrace]
  refine ⟨112992503897565896193516185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75328335931710597462344123 112992503897565896193516185)
  ·
    refine ⟨84744377923174422145137139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112992503897565896193516185 84744377923174422145137139)
    ·
      refine ⟨127116566884761633217705709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84744377923174422145137139 127116566884761633217705709)
      ·
        refine ⟨47668712581785612456639641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127116566884761633217705709 47668712581785612456639641)
        ·
          refine ⟨35751534436339209342479731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47668712581785612456639641 35751534436339209342479731)
          ·
            refine ⟨53627301654508814013719597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35751534436339209342479731 53627301654508814013719597)
            ·
              refine ⟨20110238120440805255144849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53627301654508814013719597 20110238120440805255144849)
              ·
                refine ⟨15082678590330603941358637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20110238120440805255144849 15082678590330603941358637)
                ·
                  refine ⟨5656004471373976478009489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15082678590330603941358637 5656004471373976478009489)
                  ·
                    refine ⟨4242003353530482358507117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5656004471373976478009489 4242003353530482358507117)
                    ·
                      refine ⟨1590751257573930884440169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4242003353530482358507117 1590751257573930884440169)
                      ·
                        rfl

theorem cell23_3097977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_3097977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097977 prefixEnd_3097977 := by exact prefixLift 3097977
  have htrace : WordTrace (prefixWord ++ tailWord_3097977) baseStart_3097977 baseEnd_3097977 := by
    simpa [prefixWord, tailWord_3097977, baseEnd_3097977] using wordTrace_append hprefix tailTrace_3097977
  have hstable : (prefixWord ++ tailWord_3097977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097977).length < 2 ^ (prefixWord ++ tailWord_3097977).sum := by decide
  have hdescent : baseEnd_3097977 < baseStart_3097977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097987 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4]
def baseStart_3097987 : Nat := 118140960795 + 3097987 * 2 ^ 59
def prefixEnd_3097987 : Nat := 4983230072969 + 3 ^ 40 * 3097987 * 2
def baseEnd_3097987 : Nat := 1590756392380475845315123

theorem tailTrace_3097987 : CollatzResearch.WordTrace tailWord_3097987 prefixEnd_3097987 1590756392380475845315123 := by
  unfold tailWord_3097987
  simp only [CollatzResearch.WordTrace]
  refine ⟨112992868627529667901380215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75328579085019778600920143 112992868627529667901380215)
  ·
    refine ⟨169489302941294501852070323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112992868627529667901380215 169489302941294501852070323)
    ·
      refine ⟨254233954411941752778105485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169489302941294501852070323 254233954411941752778105485)
      ·
        refine ⟨95337732904478157291789557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254233954411941752778105485 95337732904478157291789557)
        ·
          refine ⟨8937912459794827246105271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95337732904478157291789557 8937912459794827246105271)
          ·
            refine ⟨13406868689692240869157907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937912459794827246105271 13406868689692240869157907)
            ·
              refine ⟨20110303034538361303736861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406868689692240869157907 20110303034538361303736861)
              ·
                refine ⟨7541363637951885488901323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20110303034538361303736861 7541363637951885488901323)
                ·
                  refine ⟨11312045456927828233351985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7541363637951885488901323 11312045456927828233351985)
                  ·
                    refine ⟨8484034092695871175013989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11312045456927828233351985 8484034092695871175013989)
                    ·
                      refine ⟨1590756392380475845315123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8484034092695871175013989 1590756392380475845315123)
                      ·
                        rfl

theorem cell23_3097987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_3097987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097987 prefixEnd_3097987 := by exact prefixLift 3097987
  have htrace : WordTrace (prefixWord ++ tailWord_3097987) baseStart_3097987 baseEnd_3097987 := by
    simpa [prefixWord, tailWord_3097987, baseEnd_3097987] using wordTrace_append hprefix tailTrace_3097987
  have hstable : (prefixWord ++ tailWord_3097987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097987).length < 2 ^ (prefixWord ++ tailWord_3097987).sum := by decide
  have hdescent : baseEnd_3097987 < baseStart_3097987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097991 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_3097991 : Nat := 118140960795 + 3097991 * 2 ^ 59
def prefixEnd_3097991 : Nat := 4983230072969 + 3 ^ 40 * 3097991 * 2
def baseEnd_3097991 : Nat := 1590758446303093829665105

theorem tailTrace_3097991 : CollatzResearch.WordTrace tailWord_3097991 prefixEnd_3097991 1590758446303093829665105 := by
  unfold tailWord_3097991
  simp only [CollatzResearch.WordTrace]
  refine ⟨112993014519515176584525827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75328676346343451056350551 112993014519515176584525827)
  ·
    refine ⟨169489521779272764876788741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112993014519515176584525827 169489521779272764876788741)
    ·
      refine ⟨31779285333613643414397889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169489521779272764876788741 31779285333613643414397889)
      ·
        refine ⟨23834464000210232560798417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31779285333613643414397889 23834464000210232560798417)
        ·
          refine ⟨17875848000157674420598813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23834464000210232560798417 17875848000157674420598813)
          ·
            refine ⟨6703443000059127907724555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17875848000157674420598813 6703443000059127907724555)
            ·
              refine ⟨10055164500088691861586833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703443000059127907724555 10055164500088691861586833)
              ·
                refine ⟨7541373375066518896190125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10055164500088691861586833 7541373375066518896190125)
                ·
                  refine ⟨2828015015649944586071297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7541373375066518896190125 2828015015649944586071297)
                  ·
                    refine ⟨2121011261737458439553473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828015015649944586071297 2121011261737458439553473)
                    ·
                      refine ⟨1590758446303093829665105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121011261737458439553473 1590758446303093829665105)
                      ·
                        rfl

theorem cell23_3097991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_3097991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3097991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3097991 prefixEnd_3097991 := by exact prefixLift 3097991
  have htrace : WordTrace (prefixWord ++ tailWord_3097991) baseStart_3097991 baseEnd_3097991 := by
    simpa [prefixWord, tailWord_3097991, baseEnd_3097991] using wordTrace_append hprefix tailTrace_3097991
  have hstable : (prefixWord ++ tailWord_3097991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097991).length < 2 ^ (prefixWord ++ tailWord_3097991).sum := by decide
  have hdescent : baseEnd_3097991 < baseStart_3097991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098004 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3098004 : Nat := 118140960795 + 3098004 * 2 ^ 59
def prefixEnd_3098004 : Nat := 4983230072969 + 3 ^ 40 * 3098004 * 2
def baseEnd_3098004 : Nat := 1590765121551602278802545

theorem tailTrace_3098004 : CollatzResearch.WordTrace tailWord_3098004 prefixEnd_3098004 1590765121551602278802545 := by
  unfold tailWord_3098004
  simp only [CollatzResearch.WordTrace]
  refine ⟨56496744334234039902374533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75328992445645386536499377 56496744334234039902374533)
  ·
    refine ⟨10593139562668882481695225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56496744334234039902374533 10593139562668882481695225)
    ·
      refine ⟨7944854672001661861271419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10593139562668882481695225 7944854672001661861271419)
      ·
        refine ⟨11917282008002492791907129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7944854672001661861271419 11917282008002492791907129)
        ·
          refine ⟨8937961506001869593930347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11917282008002492791907129 8937961506001869593930347)
          ·
            refine ⟨13406942259002804390895521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937961506001869593930347 13406942259002804390895521)
            ·
              refine ⟨10055206694252103293171641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13406942259002804390895521 10055206694252103293171641)
              ·
                refine ⟨7541405020689077469878731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10055206694252103293171641 7541405020689077469878731)
                ·
                  refine ⟨11312107531033616204818097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7541405020689077469878731 11312107531033616204818097)
                  ·
                    refine ⟨8484080648275212153613573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11312107531033616204818097 8484080648275212153613573)
                    ·
                      refine ⟨1590765121551602278802545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8484080648275212153613573 1590765121551602278802545)
                      ·
                        rfl

theorem cell23_3098004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3098004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098004 prefixEnd_3098004 := by exact prefixLift 3098004
  have htrace : WordTrace (prefixWord ++ tailWord_3098004) baseStart_3098004 baseEnd_3098004 := by
    simpa [prefixWord, tailWord_3098004, baseEnd_3098004] using wordTrace_append hprefix tailTrace_3098004
  have hstable : (prefixWord ++ tailWord_3098004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098004).length < 2 ^ (prefixWord ++ tailWord_3098004).sum := by decide
  have hdescent : baseEnd_3098004 < baseStart_3098004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098008 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3098008 : Nat := 118140960795 + 3098008 * 2 ^ 59
def prefixEnd_3098008 : Nat := 4983230072969 + 3 ^ 40 * 3098008 * 2
def baseEnd_3098008 : Nat := 1590767175474220263152527

theorem tailTrace_3098008 : CollatzResearch.WordTrace tailWord_3098008 prefixEnd_3098008 1590767175474220263152527 := by
  unfold tailWord_3098008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56496817280226794243947339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75329089706969058991929785 56496817280226794243947339)
  ·
    refine ⟨84745225920340191365921009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56496817280226794243947339 84745225920340191365921009)
    ·
      refine ⟨63558919440255143524440757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84745225920340191365921009 63558919440255143524440757)
      ·
        refine ⟨5958648697523919705416321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63558919440255143524440757 5958648697523919705416321)
        ·
          refine ⟨4468986523142939779062241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5958648697523919705416321 4468986523142939779062241)
          ·
            refine ⟨3351739892357204834296681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4468986523142939779062241 3351739892357204834296681)
            ·
              refine ⟨2513804919267903625722511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3351739892357204834296681 2513804919267903625722511)
              ·
                refine ⟨3770707378901855438583767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513804919267903625722511 3770707378901855438583767)
                ·
                  refine ⟨5656061068352783157875651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770707378901855438583767 5656061068352783157875651)
                  ·
                    refine ⟨8484091602529174736813477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5656061068352783157875651 8484091602529174736813477)
                    ·
                      refine ⟨1590767175474220263152527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8484091602529174736813477 1590767175474220263152527)
                      ·
                        rfl

theorem cell23_3098008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3098008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098008 prefixEnd_3098008 := by exact prefixLift 3098008
  have htrace : WordTrace (prefixWord ++ tailWord_3098008) baseStart_3098008 baseEnd_3098008 := by
    simpa [prefixWord, tailWord_3098008, baseEnd_3098008] using wordTrace_append hprefix tailTrace_3098008
  have hstable : (prefixWord ++ tailWord_3098008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098008).length < 2 ^ (prefixWord ++ tailWord_3098008).sum := by decide
  have hdescent : baseEnd_3098008 < baseStart_3098008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098014 : List Nat := [4, 3, 1, 2, 2, 1, 10]
def baseStart_3098014 : Nat := 118140960795 + 3098014 * 2 ^ 59
def prefixEnd_3098014 : Nat := 4983230072969 + 3 ^ 40 * 3098014 * 2
def baseEnd_3098014 : Nat := 19639138967384533823179

theorem tailTrace_3098014 : CollatzResearch.WordTrace tailWord_3098014 prefixEnd_3098014 19639138967384533823179 := by
  unfold tailWord_3098014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14124231674803981439076637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75329235598954567675075397 14124231674803981439076637)
  ·
    refine ⟨5296586878051493039653739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14124231674803981439076637 5296586878051493039653739)
    ·
      refine ⟨7944880317077239559480609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5296586878051493039653739 7944880317077239559480609)
      ·
        refine ⟨5958660237807929669610457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7944880317077239559480609 5958660237807929669610457)
        ·
          refine ⟨4468995178355947252207843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5958660237807929669610457 4468995178355947252207843)
          ·
            refine ⟨6703492767533920878311765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468995178355947252207843 6703492767533920878311765)
            ·
              refine ⟨19639138967384533823179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6703492767533920878311765 19639138967384533823179)
              ·
                rfl

theorem cell23_3098014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 10].length) (baseStart_3098014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098014 prefixEnd_3098014 := by exact prefixLift 3098014
  have htrace : WordTrace (prefixWord ++ tailWord_3098014) baseStart_3098014 baseEnd_3098014 := by
    simpa [prefixWord, tailWord_3098014, baseEnd_3098014] using wordTrace_append hprefix tailTrace_3098014
  have hstable : (prefixWord ++ tailWord_3098014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098014).length < 2 ^ (prefixWord ++ tailWord_3098014).sum := by decide
  have hdescent : baseEnd_3098014 < baseStart_3098014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098034 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_3098034 : Nat := 118140960795 + 3098034 * 2 ^ 59
def prefixEnd_3098034 : Nat := 4983230072969 + 3 ^ 40 * 3098034 * 2
def baseEnd_3098034 : Nat := 1590780525971237161427407

theorem tailTrace_3098034 : CollatzResearch.WordTrace tailWord_3098034 prefixEnd_3098034 1590780525971237161427407 := by
  unfold tailWord_3098034
  simp only [CollatzResearch.WordTrace]
  refine ⟨28248645714589848732085289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75329721905572929952227437 28248645714589848732085289)
  ·
    refine ⟨21186484285942386549063967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28248645714589848732085289 21186484285942386549063967)
    ·
      refine ⟨31779726428913579823595951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21186484285942386549063967 31779726428913579823595951)
      ·
        refine ⟨47669589643370369735393927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31779726428913579823595951 47669589643370369735393927)
        ·
          refine ⟨71504384465055554603090891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47669589643370369735393927 71504384465055554603090891)
          ·
            refine ⟨107256576697583331904636337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71504384465055554603090891 107256576697583331904636337)
            ·
              refine ⟨80442432523187498928477253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107256576697583331904636337 80442432523187498928477253)
              ·
                refine ⟨15082956098097656049089485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80442432523187498928477253 15082956098097656049089485)
                ·
                  refine ⟨5656108536786621018408557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15082956098097656049089485 5656108536786621018408557)
                  ·
                    refine ⟨2121040701294982881903209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5656108536786621018408557 2121040701294982881903209)
                    ·
                      refine ⟨1590780525971237161427407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121040701294982881903209 1590780525971237161427407)
                      ·
                        rfl

theorem cell23_3098034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_3098034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098034 prefixEnd_3098034 := by exact prefixLift 3098034
  have htrace : WordTrace (prefixWord ++ tailWord_3098034) baseStart_3098034 baseEnd_3098034 := by
    simpa [prefixWord, tailWord_3098034, baseEnd_3098034] using wordTrace_append hprefix tailTrace_3098034
  have hstable : (prefixWord ++ tailWord_3098034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098034).length < 2 ^ (prefixWord ++ tailWord_3098034).sum := by decide
  have hdescent : baseEnd_3098034 < baseStart_3098034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098041 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3098041 : Nat := 118140960795 + 3098041 * 2 ^ 59
def prefixEnd_3098041 : Nat := 4983230072969 + 3 ^ 40 * 3098041 * 2
def baseEnd_3098041 : Nat := 1590784120335818634039875

theorem tailTrace_3098041 : CollatzResearch.WordTrace tailWord_3098041 prefixEnd_3098041 1590784120335818634039875 := by
  unfold tailWord_3098041
  simp only [CollatzResearch.WordTrace]
  refine ⟨112994838169334035123845977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75329892112889356749230651 112994838169334035123845977)
  ·
    refine ⟨84746128627000526342884483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112994838169334035123845977 84746128627000526342884483)
    ·
      refine ⟨127119192940500789514326725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84746128627000526342884483 127119192940500789514326725)
      ·
        refine ⟨23834848676343898033936261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127119192940500789514326725 23834848676343898033936261)
        ·
          refine ⟨4469034126814480881363049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23834848676343898033936261 4469034126814480881363049)
          ·
            refine ⟨3351775595110860661022287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469034126814480881363049 3351775595110860661022287)
            ·
              refine ⟨5027663392666290991533431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351775595110860661022287 5027663392666290991533431)
              ·
                refine ⟨7541495088999436487300147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027663392666290991533431 7541495088999436487300147)
                ·
                  refine ⟨11312242633499154730950221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7541495088999436487300147 11312242633499154730950221)
                  ·
                    refine ⟨4242090987562183024106333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11312242633499154730950221 4242090987562183024106333)
                    ·
                      refine ⟨1590784120335818634039875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4242090987562183024106333 1590784120335818634039875)
                      ·
                        rfl

theorem cell23_3098041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3098041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098041 prefixEnd_3098041 := by exact prefixLift 3098041
  have htrace : WordTrace (prefixWord ++ tailWord_3098041) baseStart_3098041 baseEnd_3098041 := by
    simpa [prefixWord, tailWord_3098041, baseEnd_3098041] using wordTrace_append hprefix tailTrace_3098041
  have hstable : (prefixWord ++ tailWord_3098041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098041).length < 2 ^ (prefixWord ++ tailWord_3098041).sum := by decide
  have hdescent : baseEnd_3098041 < baseStart_3098041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098081 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_3098081 : Nat := 118140960795 + 3098081 * 2 ^ 59
def prefixEnd_3098081 : Nat := 4983230072969 + 3 ^ 40 * 3098081 * 2
def baseEnd_3098081 : Nat := 1590804659561998477539691

theorem tailTrace_3098081 : CollatzResearch.WordTrace tailWord_3098081 prefixEnd_3098081 1590804659561998477539691 := by
  unfold tailWord_3098081
  simp only [CollatzResearch.WordTrace]
  refine ⟨112996297089189121955302097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75330864726126081303534731 112996297089189121955302097)
  ·
    refine ⟨84747222816891841466476573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112996297089189121955302097 84747222816891841466476573)
    ·
      refine ⟨31780208556334440549928715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84747222816891841466476573 31780208556334440549928715)
      ·
        refine ⟨47670312834501660824893073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31780208556334440549928715 47670312834501660824893073)
        ·
          refine ⟨35752734625876245618669805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47670312834501660824893073 35752734625876245618669805)
          ·
            refine ⟨13407275484703592107001177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35752734625876245618669805 13407275484703592107001177)
            ·
              refine ⟨10055456613527694080250883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13407275484703592107001177 10055456613527694080250883)
              ·
                refine ⟨15083184920291541120376325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10055456613527694080250883 15083184920291541120376325)
                ·
                  refine ⟨2828097172554663960070561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15083184920291541120376325 2828097172554663960070561)
                  ·
                    refine ⟨2121072879415997970052921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828097172554663960070561 2121072879415997970052921)
                    ·
                      refine ⟨1590804659561998477539691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121072879415997970052921 1590804659561998477539691)
                      ·
                        rfl

theorem cell23_3098081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_3098081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098081 prefixEnd_3098081 := by exact prefixLift 3098081
  have htrace : WordTrace (prefixWord ++ tailWord_3098081) baseStart_3098081 baseEnd_3098081 := by
    simpa [prefixWord, tailWord_3098081, baseEnd_3098081] using wordTrace_append hprefix tailTrace_3098081
  have hstable : (prefixWord ++ tailWord_3098081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098081).length < 2 ^ (prefixWord ++ tailWord_3098081).sum := by decide
  have hdescent : baseEnd_3098081 < baseStart_3098081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098132 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3098132 : Nat := 118140960795 + 3098132 * 2 ^ 59
def prefixEnd_3098132 : Nat := 4983230072969 + 3 ^ 40 * 3098132 * 2
def baseEnd_3098132 : Nat := 1590830847075377778001957

theorem tailTrace_3098132 : CollatzResearch.WordTrace tailWord_3098132 prefixEnd_3098132 1590830847075377778001957 := by
  unfold tailWord_3098132
  simp only [CollatzResearch.WordTrace]
  refine ⟨56499078606002178832704325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75332104808002905110272433 56499078606002178832704325)
  ·
    refine ⟨10593577238625408531132061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56499078606002178832704325 10593577238625408531132061)
    ·
      refine ⟨3972591464484528199174523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10593577238625408531132061 3972591464484528199174523)
      ·
        refine ⟨5958887196726792298761785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972591464484528199174523 5958887196726792298761785)
        ·
          refine ⟨4469165397545094224071339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5958887196726792298761785 4469165397545094224071339)
          ·
            refine ⟨6703748096317641336107009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469165397545094224071339 6703748096317641336107009)
            ·
              refine ⟨5027811072238231002080257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6703748096317641336107009 5027811072238231002080257)
              ·
                refine ⟨3770858304178673251560193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5027811072238231002080257 3770858304178673251560193)
                ·
                  refine ⟨2828143728134004938670145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3770858304178673251560193 2828143728134004938670145)
                  ·
                    refine ⟨2121107796100503704002609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828143728134004938670145 2121107796100503704002609)
                    ·
                      refine ⟨1590830847075377778001957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121107796100503704002609 1590830847075377778001957)
                      ·
                        rfl

theorem cell23_3098132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3098132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098132 prefixEnd_3098132 := by exact prefixLift 3098132
  have htrace : WordTrace (prefixWord ++ tailWord_3098132) baseStart_3098132 baseEnd_3098132 := by
    simpa [prefixWord, tailWord_3098132, baseEnd_3098132] using wordTrace_append hprefix tailTrace_3098132
  have hstable : (prefixWord ++ tailWord_3098132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098132).length < 2 ^ (prefixWord ++ tailWord_3098132).sum := by decide
  have hdescent : baseEnd_3098132 < baseStart_3098132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098144 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3098144 : Nat := 118140960795 + 3098144 * 2 ^ 59
def prefixEnd_3098144 : Nat := 4983230072969 + 3 ^ 40 * 3098144 * 2
def baseEnd_3098144 : Nat := 1590837008843231731051901

theorem tailTrace_3098144 : CollatzResearch.WordTrace tailWord_3098144 prefixEnd_3098144 1590837008843231731051901 := by
  unfold tailWord_3098144
  simp only [CollatzResearch.WordTrace]
  refine ⟨56499297443980441857422743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75332396591973922476563657 56499297443980441857422743)
  ·
    refine ⟨84748946165970662786134115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56499297443980441857422743 84748946165970662786134115)
    ·
      refine ⟨127123419248955994179201173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84748946165970662786134115 127123419248955994179201173)
      ·
        refine ⟨5958910277294812227150055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127123419248955994179201173 5958910277294812227150055)
        ·
          refine ⟨8938365415942218340725083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958910277294812227150055 8938365415942218340725083)
          ·
            refine ⟨13407548123913327511087625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8938365415942218340725083 13407548123913327511087625)
            ·
              refine ⟨10055661092934995633315719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13407548123913327511087625 10055661092934995633315719)
              ·
                refine ⟨15083491639402493449973579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10055661092934995633315719 15083491639402493449973579)
                ·
                  refine ⟨22625237459103740174960369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15083491639402493449973579 22625237459103740174960369)
                  ·
                    refine ⟨16968928094327805131220277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22625237459103740174960369 16968928094327805131220277)
                    ·
                      refine ⟨1590837008843231731051901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16968928094327805131220277 1590837008843231731051901)
                      ·
                        rfl

theorem cell23_3098144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3098144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098144 prefixEnd_3098144 := by exact prefixLift 3098144
  have htrace : WordTrace (prefixWord ++ tailWord_3098144) baseStart_3098144 baseEnd_3098144 := by
    simpa [prefixWord, tailWord_3098144, baseEnd_3098144] using wordTrace_append hprefix tailTrace_3098144
  have hstable : (prefixWord ++ tailWord_3098144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098144).length < 2 ^ (prefixWord ++ tailWord_3098144).sum := by decide
  have hdescent : baseEnd_3098144 < baseStart_3098144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098154 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3098154 : Nat := 118140960795 + 3098154 * 2 ^ 59
def prefixEnd_3098154 : Nat := 4983230072969 + 3 ^ 40 * 3098154 * 2
def baseEnd_3098154 : Nat := 1590842143649776691926855

theorem tailTrace_3098154 : CollatzResearch.WordTrace tailWord_3098154 prefixEnd_3098154 1590842143649776691926855 := by
  unfold tailWord_3098154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28249739904481163855677379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75332639745283103615139677 28249739904481163855677379)
  ·
    refine ⟨42374609856721745783516069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28249739904481163855677379 42374609856721745783516069)
    ·
      refine ⟨7945239348135327334409263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42374609856721745783516069 7945239348135327334409263)
      ·
        refine ⟨11917859022202991001613895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7945239348135327334409263 11917859022202991001613895)
        ·
          refine ⟨17876788533304486502420843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11917859022202991001613895 17876788533304486502420843)
          ·
            refine ⟨26815182799956729753631265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17876788533304486502420843 26815182799956729753631265)
            ·
              refine ⟨20111387099967547315223449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26815182799956729753631265 20111387099967547315223449)
              ·
                refine ⟨15083540324975660486417587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20111387099967547315223449 15083540324975660486417587)
                ·
                  refine ⟨22625310487463490729626381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15083540324975660486417587 22625310487463490729626381)
                  ·
                    refine ⟨8484491432798809023609893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22625310487463490729626381 8484491432798809023609893)
                    ·
                      refine ⟨1590842143649776691926855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8484491432798809023609893 1590842143649776691926855)
                      ·
                        rfl

theorem cell23_3098154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3098154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098154 prefixEnd_3098154 := by exact prefixLift 3098154
  have htrace : WordTrace (prefixWord ++ tailWord_3098154) baseStart_3098154 baseEnd_3098154 := by
    simpa [prefixWord, tailWord_3098154, baseEnd_3098154] using wordTrace_append hprefix tailTrace_3098154
  have hstable : (prefixWord ++ tailWord_3098154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098154).length < 2 ^ (prefixWord ++ tailWord_3098154).sum := by decide
  have hdescent : baseEnd_3098154 < baseStart_3098154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098194 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3098194 : Nat := 118140960795 + 3098194 * 2 ^ 59
def prefixEnd_3098194 : Nat := 4983230072969 + 3 ^ 40 * 3098194 * 2
def baseEnd_3098194 : Nat := 176762520319550726158519

theorem tailTrace_3098194 : CollatzResearch.WordTrace tailWord_3098194 prefixEnd_3098194 176762520319550726158519 := by
  unfold tailWord_3098194
  simp only [CollatzResearch.WordTrace]
  refine ⟨28250104634444935563541409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75333612358519828169443757 28250104634444935563541409)
  ·
    refine ⟨21187578475833701672656057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28250104634444935563541409 21187578475833701672656057)
    ·
      refine ⟨15890683856875276254492043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21187578475833701672656057 15890683856875276254492043)
      ·
        refine ⟨23836025785312914381738065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15890683856875276254492043 23836025785312914381738065)
        ·
          refine ⟨17877019338984685786303549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23836025785312914381738065 17877019338984685786303549)
          ·
            refine ⟨6703882252119257169863831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17877019338984685786303549 6703882252119257169863831)
            ·
              refine ⟨10055823378178885754795747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703882252119257169863831 10055823378178885754795747)
              ·
                refine ⟨15083735067268328632193621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10055823378178885754795747 15083735067268328632193621)
                ·
                  refine ⟨176762520319550726158519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15083735067268328632193621 176762520319550726158519)
                  ·
                    rfl

theorem cell23_3098194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3098194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098194 prefixEnd_3098194 := by exact prefixLift 3098194
  have htrace : WordTrace (prefixWord ++ tailWord_3098194) baseStart_3098194 baseEnd_3098194 := by
    simpa [prefixWord, tailWord_3098194, baseEnd_3098194] using wordTrace_append hprefix tailTrace_3098194
  have hstable : (prefixWord ++ tailWord_3098194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098194).length < 2 ^ (prefixWord ++ tailWord_3098194).sum := by decide
  have hdescent : baseEnd_3098194 < baseStart_3098194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098211 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 6]
def baseStart_3098211 : Nat := 118140960795 + 3098211 * 2 ^ 59
def prefixEnd_3098211 : Nat := 4983230072969 + 3 ^ 40 * 3098211 * 2
def baseEnd_3098211 : Nat := 176763490227453663212677

theorem tailTrace_3098211 : CollatzResearch.WordTrace tailWord_3098211 prefixEnd_3098211 176763490227453663212677 := by
  unfold tailWord_3098211
  simp only [CollatzResearch.WordTrace]
  refine ⟨113001038578718154157534487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75334025719145436105022991 113001038578718154157534487)
  ·
    refine ⟨169501557868077231236301731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113001038578718154157534487 169501557868077231236301731)
    ·
      refine ⟨254252336802115846854452597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169501557868077231236301731 254252336802115846854452597)
      ·
        refine ⟨23836156575198360642604931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254252336802115846854452597 23836156575198360642604931)
        ·
          refine ⟨35754234862797540963907397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23836156575198360642604931 35754234862797540963907397)
          ·
            refine ⟨6703919036774538930732637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35754234862797540963907397 6703919036774538930732637)
            ·
              refine ⟨2513969638790452099024739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6703919036774538930732637 2513969638790452099024739)
              ·
                refine ⟨3770954458185678148537109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513969638790452099024739 3770954458185678148537109)
                ·
                  refine ⟨176763490227453663212677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3770954458185678148537109 176763490227453663212677)
                  ·
                    rfl

theorem cell23_3098211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 6].length) (baseStart_3098211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098211 prefixEnd_3098211 := by exact prefixLift 3098211
  have htrace : WordTrace (prefixWord ++ tailWord_3098211) baseStart_3098211 baseEnd_3098211 := by
    simpa [prefixWord, tailWord_3098211, baseEnd_3098211] using wordTrace_append hprefix tailTrace_3098211
  have hstable : (prefixWord ++ tailWord_3098211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098211).length < 2 ^ (prefixWord ++ tailWord_3098211).sum := by decide
  have hdescent : baseEnd_3098211 < baseStart_3098211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098217 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_3098217 : Nat := 118140960795 + 3098217 * 2 ^ 59
def prefixEnd_3098217 : Nat := 4983230072969 + 3 ^ 40 * 3098217 * 2
def baseEnd_3098217 : Nat := 1590874492931009945439065

theorem tailTrace_3098217 : CollatzResearch.WordTrace tailWord_3098217 prefixEnd_3098217 1590874492931009945439065 := by
  unfold tailWord_3098217
  simp only [CollatzResearch.WordTrace]
  refine ⟨113001257416696417182252905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75334171611130944788168603 113001257416696417182252905)
  ·
    refine ⟨84750943062522312886689679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113001257416696417182252905 84750943062522312886689679)
    ·
      refine ⟨127126414593783469330034519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84750943062522312886689679 127126414593783469330034519)
      ·
        refine ⟨190689621890675203995051779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127126414593783469330034519 190689621890675203995051779)
        ·
          refine ⟨286034432836012805992577669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190689621890675203995051779 286034432836012805992577669)
          ·
            refine ⟨53631456156752401123608313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286034432836012805992577669 53631456156752401123608313)
            ·
              refine ⟨40223592117564300842706235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53631456156752401123608313 40223592117564300842706235)
              ·
                refine ⟨60335388176346451264059353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40223592117564300842706235 60335388176346451264059353)
                ·
                  refine ⟨45251541132259838448044515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60335388176346451264059353 45251541132259838448044515)
                  ·
                    refine ⟨67877311698389757672066773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45251541132259838448044515 67877311698389757672066773)
                    ·
                      refine ⟨1590874492931009945439065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67877311698389757672066773 1590874492931009945439065)
                      ·
                        rfl

theorem cell23_3098217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_3098217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098217 prefixEnd_3098217 := by exact prefixLift 3098217
  have htrace : WordTrace (prefixWord ++ tailWord_3098217) baseStart_3098217 baseEnd_3098217 := by
    simpa [prefixWord, tailWord_3098217, baseEnd_3098217] using wordTrace_append hprefix tailTrace_3098217
  have hstable : (prefixWord ++ tailWord_3098217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098217).length < 2 ^ (prefixWord ++ tailWord_3098217).sum := by decide
  have hdescent : baseEnd_3098217 < baseStart_3098217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098231 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 2, 3, 2]
def baseStart_3098231 : Nat := 118140960795 + 3098231 * 2 ^ 59
def prefixEnd_3098231 : Nat := 4983230072969 + 3 ^ 40 * 3098231 * 2
def baseEnd_3098231 : Nat := 1590881681660172890664001

theorem tailTrace_3098231 : CollatzResearch.WordTrace tailWord_3098231 prefixEnd_3098231 1590881681660172890664001 := by
  unfold tailWord_3098231
  simp only [CollatzResearch.WordTrace]
  refine ⟨113001768038645697573262547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75334512025763798382175031 113001768038645697573262547)
  ·
    refine ⟨169502652057968546359893821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113001768038645697573262547 169502652057968546359893821)
    ·
      refine ⟨63563494521738204884960183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169502652057968546359893821 63563494521738204884960183)
      ·
        refine ⟨95345241782607307327440275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63563494521738204884960183 95345241782607307327440275)
        ·
          refine ⟨143017862673910960991160413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95345241782607307327440275 143017862673910960991160413)
          ·
            refine ⟨53631698502716610371685155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143017862673910960991160413 53631698502716610371685155)
            ·
              refine ⟨80447547754074915557527733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53631698502716610371685155 80447547754074915557527733)
              ·
                refine ⟨7541957601944523333518225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80447547754074915557527733 7541957601944523333518225)
                ·
                  refine ⟨5656468201458392500138669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541957601944523333518225 5656468201458392500138669)
                  ·
                    refine ⟨2121175575546897187552001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5656468201458392500138669 2121175575546897187552001)
                    ·
                      refine ⟨1590881681660172890664001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121175575546897187552001 1590881681660172890664001)
                      ·
                        rfl

theorem cell23_3098231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_3098231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098231 prefixEnd_3098231 := by exact prefixLift 3098231
  have htrace : WordTrace (prefixWord ++ tailWord_3098231) baseStart_3098231 baseEnd_3098231 := by
    simpa [prefixWord, tailWord_3098231, baseEnd_3098231] using wordTrace_append hprefix tailTrace_3098231
  have hstable : (prefixWord ++ tailWord_3098231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098231).length < 2 ^ (prefixWord ++ tailWord_3098231).sum := by decide
  have hdescent : baseEnd_3098231 < baseStart_3098231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098241 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3098241 : Nat := 118140960795 + 3098241 * 2 ^ 59
def prefixEnd_3098241 : Nat := 4983230072969 + 3 ^ 40 * 3098241 * 2
def baseEnd_3098241 : Nat := 530295605488905950512985

theorem tailTrace_3098241 : CollatzResearch.WordTrace tailWord_3098241 prefixEnd_3098241 530295605488905950512985 := by
  unfold tailWord_3098241
  simp only [CollatzResearch.WordTrace]
  refine ⟨113002132768609469281126577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75334755179072979520751051 113002132768609469281126577)
  ·
    refine ⟨84751599576457101960844933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113002132768609469281126577 84751599576457101960844933)
    ·
      refine ⟨15890924920585706617658425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84751599576457101960844933 15890924920585706617658425)
      ·
        refine ⟨11918193690439279963243819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15890924920585706617658425 11918193690439279963243819)
        ·
          refine ⟨17877290535658919944865729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918193690439279963243819 17877290535658919944865729)
          ·
            refine ⟨13407967901744189958649297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17877290535658919944865729 13407967901744189958649297)
            ·
              refine ⟨10055975926308142468986973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13407967901744189958649297 10055975926308142468986973)
              ·
                refine ⟨3770990972365553425870115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10055975926308142468986973 3770990972365553425870115)
                ·
                  refine ⟨5656486458548330138805173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770990972365553425870115 5656486458548330138805173)
                  ·
                    refine ⟨530295605488905950512985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5656486458548330138805173 530295605488905950512985)
                    ·
                      rfl

theorem cell23_3098241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3098241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098241 prefixEnd_3098241 := by exact prefixLift 3098241
  have htrace : WordTrace (prefixWord ++ tailWord_3098241) baseStart_3098241 baseEnd_3098241 := by
    simpa [prefixWord, tailWord_3098241, baseEnd_3098241] using wordTrace_append hprefix tailTrace_3098241
  have hstable : (prefixWord ++ tailWord_3098241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098241).length < 2 ^ (prefixWord ++ tailWord_3098241).sum := by decide
  have hdescent : baseEnd_3098241 < baseStart_3098241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098306 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3098306 : Nat := 118140960795 + 3098306 * 2 ^ 59
def prefixEnd_3098306 : Nat := 4983230072969 + 3 ^ 40 * 3098306 * 2
def baseEnd_3098306 : Nat := 1590920192709260097226157

theorem tailTrace_3098306 : CollatzResearch.WordTrace tailWord_3098306 prefixEnd_3098306 1590920192709260097226157 := by
  unfold tailWord_3098306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251125878343496345560693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75336335675582656921495181 28251125878343496345560693)
  ·
    refine ⟨2648543051094702782396315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28251125878343496345560693 2648543051094702782396315)
    ·
      refine ⟨3972814576642054173594473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648543051094702782396315 3972814576642054173594473)
      ·
        refine ⟨2979610932481540630195855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3972814576642054173594473 2979610932481540630195855)
        ·
          refine ⟨4469416398722310945293783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979610932481540630195855 4469416398722310945293783)
          ·
            refine ⟨6704124598083466417940675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469416398722310945293783 6704124598083466417940675)
            ·
              refine ⟨10056186897125199626911013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6704124598083466417940675 10056186897125199626911013)
              ·
                refine ⟨1885535043210974930045815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10056186897125199626911013 1885535043210974930045815)
                ·
                  refine ⟨2828302564816462395068723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885535043210974930045815 2828302564816462395068723)
                  ·
                    refine ⟨4242453847224693592603085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2828302564816462395068723 4242453847224693592603085)
                    ·
                      refine ⟨1590920192709260097226157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4242453847224693592603085 1590920192709260097226157)
                      ·
                        rfl

theorem cell23_3098306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3098306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098306 prefixEnd_3098306 := by exact prefixLift 3098306
  have htrace : WordTrace (prefixWord ++ tailWord_3098306) baseStart_3098306 baseEnd_3098306 := by
    simpa [prefixWord, tailWord_3098306, baseEnd_3098306] using wordTrace_append hprefix tailTrace_3098306
  have hstable : (prefixWord ++ tailWord_3098306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098306).length < 2 ^ (prefixWord ++ tailWord_3098306).sum := by decide
  have hdescent : baseEnd_3098306 < baseStart_3098306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098328 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3098328 : Nat := 118140960795 + 3098328 * 2 ^ 59
def prefixEnd_3098328 : Nat := 4983230072969 + 3 ^ 40 * 3098328 * 2
def baseEnd_3098328 : Nat := 1590931489283659011151055

theorem tailTrace_3098328 : CollatzResearch.WordTrace tailWord_3098328 prefixEnd_3098328 1590931489283659011151055 := by
  unfold tailWord_3098328
  simp only [CollatzResearch.WordTrace]
  refine ⟨56502652959647141569771819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75336870612862855426362425 56502652959647141569771819)
  ·
    refine ⟨84753979439470712354657729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56502652959647141569771819 84753979439470712354657729)
    ·
      refine ⟨63565484579603034265993297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84753979439470712354657729 63565484579603034265993297)
      ·
        refine ⟨47674113434702275699494973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63565484579603034265993297 47674113434702275699494973)
        ·
          refine ⟨17877792538013353387310615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47674113434702275699494973 17877792538013353387310615)
          ·
            refine ⟨26816688807020030080965923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17877792538013353387310615 26816688807020030080965923)
            ·
              refine ⟨40225033210530045121448885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26816688807020030080965923 40225033210530045121448885)
              ·
                refine ⟨3771096863487191730135833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40225033210530045121448885 3771096863487191730135833)
                ·
                  refine ⟨2828322647615393797601875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3771096863487191730135833 2828322647615393797601875)
                  ·
                    refine ⟨4242483971423090696402813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2828322647615393797601875 4242483971423090696402813)
                    ·
                      refine ⟨1590931489283659011151055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4242483971423090696402813 1590931489283659011151055)
                      ·
                        rfl

theorem cell23_3098328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3098328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098328 prefixEnd_3098328 := by exact prefixLift 3098328
  have htrace : WordTrace (prefixWord ++ tailWord_3098328) baseStart_3098328 baseEnd_3098328 := by
    simpa [prefixWord, tailWord_3098328, baseEnd_3098328] using wordTrace_append hprefix tailTrace_3098328
  have hstable : (prefixWord ++ tailWord_3098328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098328).length < 2 ^ (prefixWord ++ tailWord_3098328).sum := by decide
  have hdescent : baseEnd_3098328 < baseStart_3098328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098355 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 1, 3, 2]
def baseStart_3098355 : Nat := 118140960795 + 3098355 * 2 ^ 59
def prefixEnd_3098355 : Nat := 4983230072969 + 3 ^ 40 * 3098355 * 2
def baseEnd_3098355 : Nat := 1590945353261330405513431

theorem tailTrace_3098355 : CollatzResearch.WordTrace tailWord_3098355 prefixEnd_3098355 1590945353261330405513431 := by
  unfold tailWord_3098355
  simp only [CollatzResearch.WordTrace]
  refine ⟨113006290690196466750776519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75337527126797644500517679 113006290690196466750776519)
  ·
    refine ⟨169509436035294700126164779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113006290690196466750776519 169509436035294700126164779)
    ·
      refine ⟨254264154052942050189247169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169509436035294700126164779 254264154052942050189247169)
      ·
        refine ⟨190698115539706537641935377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254264154052942050189247169 190698115539706537641935377)
        ·
          refine ⟨143023586654779903231451533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190698115539706537641935377 143023586654779903231451533)
          ·
            refine ⟨53633844995542463711794325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143023586654779903231451533 53633844995542463711794325)
            ·
              refine ⟨2514086484166052986490359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53633844995542463711794325 2514086484166052986490359)
              ·
                refine ⟨3771129726249079479735539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514086484166052986490359 3771129726249079479735539)
                ·
                  refine ⟨5656694589373619219603309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771129726249079479735539 5656694589373619219603309)
                  ·
                    refine ⟨2121260471015107207351241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5656694589373619219603309 2121260471015107207351241)
                    ·
                      refine ⟨1590945353261330405513431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121260471015107207351241 1590945353261330405513431)
                      ·
                        rfl

theorem cell23_3098355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 3, 2].length) (baseStart_3098355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098355 prefixEnd_3098355 := by exact prefixLift 3098355
  have htrace : WordTrace (prefixWord ++ tailWord_3098355) baseStart_3098355 baseEnd_3098355 := by
    simpa [prefixWord, tailWord_3098355, baseEnd_3098355] using wordTrace_append hprefix tailTrace_3098355
  have hstable : (prefixWord ++ tailWord_3098355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098355).length < 2 ^ (prefixWord ++ tailWord_3098355).sum := by decide
  have hdescent : baseEnd_3098355 < baseStart_3098355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098368 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 4, 2, 2]
def baseStart_3098368 : Nat := 118140960795 + 3098368 * 2 ^ 59
def prefixEnd_3098368 : Nat := 4983230072969 + 3 ^ 40 * 3098368 * 2
def baseEnd_3098368 : Nat := 1590952028509838854650871

theorem tailTrace_3098368 : CollatzResearch.WordTrace tailWord_3098368 prefixEnd_3098368 1590952028509838854650871 := by
  unfold tailWord_3098368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56503382419574684985499879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75337843226099579980666505 56503382419574684985499879)
  ·
    refine ⟨84755073629362027478249819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56503382419574684985499879 84755073629362027478249819)
    ·
      refine ⟨127132610444043041217374729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84755073629362027478249819 127132610444043041217374729)
      ·
        refine ⟨95349457833032280913031047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127132610444043041217374729 95349457833032280913031047)
        ·
          refine ⟨143024186749548421369546571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95349457833032280913031047 143024186749548421369546571)
          ·
            refine ⟨214536280124322632054319857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143024186749548421369546571 214536280124322632054319857)
            ·
              refine ⟨160902210093241974040739893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214536280124322632054319857 160902210093241974040739893)
              ·
                refine ⟨15084582196241435066319365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160902210093241974040739893 15084582196241435066319365)
                ·
                  refine ⟨2828359161795269074934881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15084582196241435066319365 2828359161795269074934881)
                  ·
                    refine ⟨2121269371346451806201161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828359161795269074934881 2121269371346451806201161)
                    ·
                      refine ⟨1590952028509838854650871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121269371346451806201161 1590952028509838854650871)
                      ·
                        rfl

theorem cell23_3098368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_3098368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098368 prefixEnd_3098368 := by exact prefixLift 3098368
  have htrace : WordTrace (prefixWord ++ tailWord_3098368) baseStart_3098368 baseEnd_3098368 := by
    simpa [prefixWord, tailWord_3098368, baseEnd_3098368] using wordTrace_append hprefix tailTrace_3098368
  have hstable : (prefixWord ++ tailWord_3098368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098368).length < 2 ^ (prefixWord ++ tailWord_3098368).sum := by decide
  have hdescent : baseEnd_3098368 < baseStart_3098368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098391 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 7]
def baseStart_3098391 : Nat := 118140960795 + 3098391 * 2 ^ 59
def prefixEnd_3098391 : Nat := 4983230072969 + 3 ^ 40 * 3098391 * 2
def baseEnd_3098391 : Nat := 176773759840543584962585

theorem tailTrace_3098391 : CollatzResearch.WordTrace tailWord_3098391 prefixEnd_3098391 176773759840543584962585 := by
  unfold tailWord_3098391
  simp only [CollatzResearch.WordTrace]
  refine ⟨113007603718066044899087027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75338402478710696599391351 113007603718066044899087027)
  ·
    refine ⟨169511405577099067348630541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113007603718066044899087027 169511405577099067348630541)
    ·
      refine ⟨63566777091412150255736453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169511405577099067348630541 63566777091412150255736453)
      ·
        refine ⟨11918770704639778172950585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63566777091412150255736453 11918770704639778172950585)
        ·
          refine ⟨8939078028479833629712939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11918770704639778172950585 8939078028479833629712939)
          ·
            refine ⟨13408617042719750444569409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8939078028479833629712939 13408617042719750444569409)
            ·
              refine ⟨10056462782039812833427057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13408617042719750444569409 10056462782039812833427057)
              ·
                refine ⟨7542347086529859625070293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10056462782039812833427057 7542347086529859625070293)
                ·
                  refine ⟨176773759840543584962585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7542347086529859625070293 176773759840543584962585)
                  ·
                    rfl

theorem cell23_3098391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 7].length) (baseStart_3098391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098391 prefixEnd_3098391 := by exact prefixLift 3098391
  have htrace : WordTrace (prefixWord ++ tailWord_3098391) baseStart_3098391 baseEnd_3098391 := by
    simpa [prefixWord, tailWord_3098391, baseEnd_3098391] using wordTrace_append hprefix tailTrace_3098391
  have hstable : (prefixWord ++ tailWord_3098391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098391).length < 2 ^ (prefixWord ++ tailWord_3098391).sum := by decide
  have hdescent : baseEnd_3098391 < baseStart_3098391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098425 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 7]
def baseStart_3098425 : Nat := 118140960795 + 3098425 * 2 ^ 59
def prefixEnd_3098425 : Nat := 4983230072969 + 3 ^ 40 * 3098425 * 2
def baseEnd_3098425 : Nat := 176775699656349459070901

theorem tailTrace_3098425 : CollatzResearch.WordTrace tailWord_3098425 prefixEnd_3098425 176775699656349459070901 := by
  unfold tailWord_3098425
  simp only [CollatzResearch.WordTrace]
  refine ⟨113008843799942868705824729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75339229199961912470549819 113008843799942868705824729)
  ·
    refine ⟨84756632849957151529368547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113008843799942868705824729 84756632849957151529368547)
    ·
      refine ⟨127134949274935727294052821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84756632849957151529368547 127134949274935727294052821)
      ·
        refine ⟨2979725373631306108454363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 127134949274935727294052821 2979725373631306108454363)
        ·
          refine ⟨4469588060446959162681545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979725373631306108454363 4469588060446959162681545)
          ·
            refine ⟨3352191045335219372011159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469588060446959162681545 3352191045335219372011159)
            ·
              refine ⟨5028286568002829058016739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352191045335219372011159 5028286568002829058016739)
              ·
                refine ⟨7542429852004243587025109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028286568002829058016739 7542429852004243587025109)
                ·
                  refine ⟨176775699656349459070901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7542429852004243587025109 176775699656349459070901)
                  ·
                    rfl

theorem cell23_3098425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 7].length) (baseStart_3098425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098425 prefixEnd_3098425 := by exact prefixLift 3098425
  have htrace : WordTrace (prefixWord ++ tailWord_3098425) baseStart_3098425 baseEnd_3098425 := by
    simpa [prefixWord, tailWord_3098425, baseEnd_3098425] using wordTrace_append hprefix tailTrace_3098425
  have hstable : (prefixWord ++ tailWord_3098425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098425).length < 2 ^ (prefixWord ++ tailWord_3098425).sum := by decide
  have hdescent : baseEnd_3098425 < baseStart_3098425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098441 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_3098441 : Nat := 118140960795 + 3098441 * 2 ^ 59
def prefixEnd_3098441 : Nat := 4983230072969 + 3 ^ 40 * 3098441 * 2
def baseEnd_3098441 : Nat := 1590989512597617069038035

theorem tailTrace_3098441 : CollatzResearch.WordTrace tailWord_3098441 prefixEnd_3098441 1590989512597617069038035 := by
  unfold tailWord_3098441
  simp only [CollatzResearch.WordTrace]
  refine ⟨113009427367884903438407177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75339618245256602292271451 113009427367884903438407177)
  ·
    refine ⟨84757070525913677578805383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113009427367884903438407177 84757070525913677578805383)
    ·
      refine ⟨127135605788870516368208075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84757070525913677578805383 127135605788870516368208075)
      ·
        refine ⟨190703408683305774552312113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127135605788870516368208075 190703408683305774552312113)
        ·
          refine ⟨143027556512479330914234085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190703408683305774552312113 143027556512479330914234085)
          ·
            refine ⟨26817666846089874546418891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143027556512479330914234085 26817666846089874546418891)
            ·
              refine ⟨40226500269134811819628337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26817666846089874546418891 40226500269134811819628337)
              ·
                refine ⟨30169875201851108864721253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40226500269134811819628337 30169875201851108864721253)
                ·
                  refine ⟨5656851600347082912135235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30169875201851108864721253 5656851600347082912135235)
                  ·
                    refine ⟨8485277400520624368202853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5656851600347082912135235 8485277400520624368202853)
                    ·
                      refine ⟨1590989512597617069038035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8485277400520624368202853 1590989512597617069038035)
                      ·
                        rfl

theorem cell23_3098441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_3098441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098441 prefixEnd_3098441 := by exact prefixLift 3098441
  have htrace : WordTrace (prefixWord ++ tailWord_3098441) baseStart_3098441 baseEnd_3098441 := by
    simpa [prefixWord, tailWord_3098441, baseEnd_3098441] using wordTrace_append hprefix tailTrace_3098441
  have hstable : (prefixWord ++ tailWord_3098441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098441).length < 2 ^ (prefixWord ++ tailWord_3098441).sum := by decide
  have hdescent : baseEnd_3098441 < baseStart_3098441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098458 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_3098458 : Nat := 118140960795 + 3098458 * 2 ^ 59
def prefixEnd_3098458 : Nat := 4983230072969 + 3 ^ 40 * 3098458 * 2
def baseEnd_3098458 : Nat := 1590998241768743502525457

theorem tailTrace_3098458 : CollatzResearch.WordTrace tailWord_3098458 prefixEnd_3098458 1590998241768743502525457 := by
  unfold tailWord_3098458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28252511852205828835444007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75340031605882210227850685 28252511852205828835444007)
  ·
    refine ⟨42378767778308743253166011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28252511852205828835444007 42378767778308743253166011)
    ·
      refine ⟨63568151667463114879749017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42378767778308743253166011 63568151667463114879749017)
      ·
        refine ⟨47676113750597336159811763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63568151667463114879749017 47676113750597336159811763)
        ·
          refine ⟨71514170625896004239717645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47676113750597336159811763 71514170625896004239717645)
          ·
            refine ⟨26817813984711001589894117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71514170625896004239717645 26817813984711001589894117)
            ·
              refine ⟨5028340122133312798105147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26817813984711001589894117 5028340122133312798105147)
              ·
                refine ⟨7542510183199969197157721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028340122133312798105147 7542510183199969197157721)
                ·
                  refine ⟨5656882637399976897868291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542510183199969197157721 5656882637399976897868291)
                  ·
                    refine ⟨8485323956099965346802437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5656882637399976897868291 8485323956099965346802437)
                    ·
                      refine ⟨1590998241768743502525457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8485323956099965346802437 1590998241768743502525457)
                      ·
                        rfl

theorem cell23_3098458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_3098458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098458 prefixEnd_3098458 := by exact prefixLift 3098458
  have htrace : WordTrace (prefixWord ++ tailWord_3098458) baseStart_3098458 baseEnd_3098458 := by
    simpa [prefixWord, tailWord_3098458, baseEnd_3098458] using wordTrace_append hprefix tailTrace_3098458
  have hstable : (prefixWord ++ tailWord_3098458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098458).length < 2 ^ (prefixWord ++ tailWord_3098458).sum := by decide
  have hdescent : baseEnd_3098458 < baseStart_3098458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098471 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3098471 : Nat := 118140960795 + 3098471 * 2 ^ 59
def prefixEnd_3098471 : Nat := 4983230072969 + 3 ^ 40 * 3098471 * 2
def baseEnd_3098471 : Nat := 1591004917017251951662897

theorem tailTrace_3098471 : CollatzResearch.WordTrace tailWord_3098471 prefixEnd_3098471 1591004917017251951662897 := by
  unfold tailWord_3098471
  simp only [CollatzResearch.WordTrace]
  refine ⟨113010521557776218561999267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75340347705184145707999511 113010521557776218561999267)
  ·
    refine ⟨169515782336664327842998901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113010521557776218561999267 169515782336664327842998901)
    ·
      refine ⟨15892104594062280735281147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169515782336664327842998901 15892104594062280735281147)
      ·
        refine ⟨23838156891093421102921721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15892104594062280735281147 23838156891093421102921721)
        ·
          refine ⟨17878617668320065827191291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23838156891093421102921721 17878617668320065827191291)
          ·
            refine ⟨26817926502480098740786937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17878617668320065827191291 26817926502480098740786937)
            ·
              refine ⟨20113444876860074055590203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26817926502480098740786937 20113444876860074055590203)
              ·
                refine ⟨30170167315290111083385305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20113444876860074055590203 30170167315290111083385305)
                ·
                  refine ⟨22627625486467583312538979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30170167315290111083385305 22627625486467583312538979)
                  ·
                    refine ⟨33941438229701374968808469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22627625486467583312538979 33941438229701374968808469)
                    ·
                      refine ⟨1591004917017251951662897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33941438229701374968808469 1591004917017251951662897)
                      ·
                        rfl

theorem cell23_3098471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3098471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098471 prefixEnd_3098471 := by exact prefixLift 3098471
  have htrace : WordTrace (prefixWord ++ tailWord_3098471) baseStart_3098471 baseEnd_3098471 := by
    simpa [prefixWord, tailWord_3098471, baseEnd_3098471] using wordTrace_append hprefix tailTrace_3098471
  have hstable : (prefixWord ++ tailWord_3098471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098471).length < 2 ^ (prefixWord ++ tailWord_3098471).sum := by decide
  have hdescent : baseEnd_3098471 < baseStart_3098471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098491 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 3]
def baseStart_3098491 : Nat := 118140960795 + 3098491 * 2 ^ 59
def prefixEnd_3098491 : Nat := 4983230072969 + 3 ^ 40 * 3098491 * 2
def baseEnd_3098491 : Nat := 1591015186630341873412805

theorem tailTrace_3098491 : CollatzResearch.WordTrace tailWord_3098491 prefixEnd_3098491 1591015186630341873412805 := by
  unfold tailWord_3098491
  simp only [CollatzResearch.WordTrace]
  refine ⟨113011251017703761977727327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75340834011802507985151551 113011251017703761977727327)
  ·
    refine ⟨169516876526555642966590991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113011251017703761977727327 169516876526555642966590991)
    ·
      refine ⟨254275314789833464449886487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169516876526555642966590991 254275314789833464449886487)
      ·
        refine ⟨381412972184750196674829731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254275314789833464449886487 381412972184750196674829731)
        ·
          refine ⟨572119458277125295012244597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381412972184750196674829731 572119458277125295012244597)
          ·
            refine ⟨53636199213480496407397931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 572119458277125295012244597 53636199213480496407397931)
            ·
              refine ⟨80454298820220744611096897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53636199213480496407397931 80454298820220744611096897)
              ·
                refine ⟨60340724115165558458322673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80454298820220744611096897 60340724115165558458322673)
                ·
                  refine ⟨45255543086374168843742005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60340724115165558458322673 45255543086374168843742005)
                  ·
                    refine ⟨4242707164347578329100813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45255543086374168843742005 4242707164347578329100813)
                    ·
                      refine ⟨1591015186630341873412805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4242707164347578329100813 1591015186630341873412805)
                      ·
                        rfl

theorem cell23_3098491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 3].length) (baseStart_3098491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098491 prefixEnd_3098491 := by exact prefixLift 3098491
  have htrace : WordTrace (prefixWord ++ tailWord_3098491) baseStart_3098491 baseEnd_3098491 := by
    simpa [prefixWord, tailWord_3098491, baseEnd_3098491] using wordTrace_append hprefix tailTrace_3098491
  have hstable : (prefixWord ++ tailWord_3098491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098491).length < 2 ^ (prefixWord ++ tailWord_3098491).sum := by decide
  have hdescent : baseEnd_3098491 < baseStart_3098491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098565 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 5, 2, 2]
def baseStart_3098565 : Nat := 118140960795 + 3098565 * 2 ^ 59
def prefixEnd_3098565 : Nat := 4983230072969 + 3 ^ 40 * 3098565 * 2
def baseEnd_3098565 : Nat := 1591053184198774583887465

theorem tailTrace_3098565 : CollatzResearch.WordTrace tailWord_3098565 prefixEnd_3098565 1591053184198774583887465 := by
  unfold tailWord_3098565
  simp only [CollatzResearch.WordTrace]
  refine ⟨113013950019435672615921149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75342633346290448410614099 113013950019435672615921149)
  ·
    refine ⟨42380231257288377230970431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113013950019435672615921149 42380231257288377230970431)
    ·
      refine ⟨63570346885932565846455647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42380231257288377230970431 63570346885932565846455647)
      ·
        refine ⟨95355520328898848769683471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63570346885932565846455647 95355520328898848769683471)
        ·
          refine ⟨143033280493348273154525207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95355520328898848769683471 143033280493348273154525207)
          ·
            refine ⟨214549920740022409731787811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143033280493348273154525207 214549920740022409731787811)
            ·
              refine ⟨321824881110033614597681717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214549920740022409731787811 321824881110033614597681717)
              ·
                refine ⟨30171082604065651368532661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321824881110033614597681717 30171082604065651368532661)
                ·
                  refine ⟨2828538994131154815799937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30171082604065651368532661 2828538994131154815799937)
                  ·
                    refine ⟨2121404245598366111849953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828538994131154815799937 2121404245598366111849953)
                    ·
                      refine ⟨1591053184198774583887465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121404245598366111849953 1591053184198774583887465)
                      ·
                        rfl

theorem cell23_3098565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_3098565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098565 prefixEnd_3098565 := by exact prefixLift 3098565
  have htrace : WordTrace (prefixWord ++ tailWord_3098565) baseStart_3098565 baseEnd_3098565 := by
    simpa [prefixWord, tailWord_3098565, baseEnd_3098565] using wordTrace_append hprefix tailTrace_3098565
  have hstable : (prefixWord ++ tailWord_3098565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098565).length < 2 ^ (prefixWord ++ tailWord_3098565).sum := by decide
  have hdescent : baseEnd_3098565 < baseStart_3098565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098571 : List Nat := [1, 1, 1, 1, 3, 4, 3, 9]
def baseStart_3098571 : Nat := 118140960795 + 3098571 * 2 ^ 59
def prefixEnd_3098571 : Nat := 4983230072969 + 3 ^ 40 * 3098571 * 2
def baseEnd_3098571 : Nat := 58928009817877835570831

theorem tailTrace_3098571 : CollatzResearch.WordTrace tailWord_3098571 prefixEnd_3098571 58928009817877835570831 := by
  unfold tailWord_3098571
  simp only [CollatzResearch.WordTrace]
  refine ⟨113014168857413935640639567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75342779238275957093759711 113014168857413935640639567)
  ·
    refine ⟨169521253286120903460959351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113014168857413935640639567 169521253286120903460959351)
    ·
      refine ⟨254281879929181355191439027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169521253286120903460959351 254281879929181355191439027)
      ·
        refine ⟨381422819893772032787158541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254281879929181355191439027 381422819893772032787158541)
        ·
          refine ⟨143033557460164512295184453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381422819893772032787158541 143033557460164512295184453)
          ·
            refine ⟨26818792023780846055347085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143033557460164512295184453 26818792023780846055347085)
            ·
              refine ⟨10057047008917817270755157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26818792023780846055347085 10057047008917817270755157)
              ·
                refine ⟨58928009817877835570831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10057047008917817270755157 58928009817877835570831)
                ·
                  rfl

theorem cell23_3098571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 9].length) (baseStart_3098571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098571 prefixEnd_3098571 := by exact prefixLift 3098571
  have htrace : WordTrace (prefixWord ++ tailWord_3098571) baseStart_3098571 baseEnd_3098571 := by
    simpa [prefixWord, tailWord_3098571, baseEnd_3098571] using wordTrace_append hprefix tailTrace_3098571
  have hstable : (prefixWord ++ tailWord_3098571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098571).length < 2 ^ (prefixWord ++ tailWord_3098571).sum := by decide
  have hdescent : baseEnd_3098571 < baseStart_3098571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098585 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_3098585 : Nat := 118140960795 + 3098585 * 2 ^ 59
def prefixEnd_3098585 : Nat := 4983230072969 + 3 ^ 40 * 3098585 * 2
def baseEnd_3098585 : Nat := 1591063453811864505637373

theorem tailTrace_3098585 : CollatzResearch.WordTrace tailWord_3098585 prefixEnd_3098585 1591063453811864505637373 := by
  unfold tailWord_3098585
  simp only [CollatzResearch.WordTrace]
  refine ⟨113014679479363216031649209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75343119652908810687766139 113014679479363216031649209)
  ·
    refine ⟨84761009609522412023736907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113014679479363216031649209 84761009609522412023736907)
    ·
      refine ⟨127141514414283618035605361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84761009609522412023736907 127141514414283618035605361)
      ·
        refine ⟨95356135810712713526704021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127141514414283618035605361 95356135810712713526704021)
        ·
          refine ⟨4469818866127158446564251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95356135810712713526704021 4469818866127158446564251)
          ·
            refine ⟨6704728299190737669846377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469818866127158446564251 6704728299190737669846377)
            ·
              refine ⟨5028546224393053252384783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6704728299190737669846377 5028546224393053252384783)
              ·
                refine ⟨7542819336589579878577175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028546224393053252384783 7542819336589579878577175)
                ·
                  refine ⟨11314229004884369817865763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7542819336589579878577175 11314229004884369817865763)
                  ·
                    refine ⟨16971343507326554726798645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11314229004884369817865763 16971343507326554726798645)
                    ·
                      refine ⟨1591063453811864505637373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16971343507326554726798645 1591063453811864505637373)
                      ·
                        rfl

theorem cell23_3098585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_3098585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098585 prefixEnd_3098585 := by exact prefixLift 3098585
  have htrace : WordTrace (prefixWord ++ tailWord_3098585) baseStart_3098585 baseEnd_3098585 := by
    simpa [prefixWord, tailWord_3098585, baseEnd_3098585] using wordTrace_append hprefix tailTrace_3098585
  have hstable : (prefixWord ++ tailWord_3098585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098585).length < 2 ^ (prefixWord ++ tailWord_3098585).sum := by decide
  have hdescent : baseEnd_3098585 < baseStart_3098585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098609 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 2, 4]
def baseStart_3098609 : Nat := 118140960795 + 3098609 * 2 ^ 59
def prefixEnd_3098609 : Nat := 4983230072969 + 3 ^ 40 * 3098609 * 2
def baseEnd_3098609 : Nat := 530358592449190803912421

theorem tailTrace_3098609 : CollatzResearch.WordTrace tailWord_3098609 prefixEnd_3098609 530358592449190803912421 := by
  unfold tailWord_3098609
  simp only [CollatzResearch.WordTrace]
  refine ⟨113015554831276268130522881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75343703220850845420348587 113015554831276268130522881)
  ·
    refine ⟨84761666123457201097892161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113015554831276268130522881 84761666123457201097892161)
    ·
      refine ⟨63571249592592900823419121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84761666123457201097892161 63571249592592900823419121)
      ·
        refine ⟨47678437194444675617564341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63571249592592900823419121 47678437194444675617564341)
        ·
          refine ⟨4469853486979188339146657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47678437194444675617564341 4469853486979188339146657)
          ·
            refine ⟨3352390115234391254359993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469853486979188339146657 3352390115234391254359993)
            ·
              refine ⟨2514292586425793440769995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352390115234391254359993 2514292586425793440769995)
              ·
                refine ⟨3771438879638690161154993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514292586425793440769995 3771438879638690161154993)
                ·
                  refine ⟨2828579159729017620866245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3771438879638690161154993 2828579159729017620866245)
                  ·
                    refine ⟨530358592449190803912421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828579159729017620866245 530358592449190803912421)
                    ·
                      rfl

theorem cell23_3098609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_3098609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098609 prefixEnd_3098609 := by exact prefixLift 3098609
  have htrace : WordTrace (prefixWord ++ tailWord_3098609) baseStart_3098609 baseEnd_3098609 := by
    simpa [prefixWord, tailWord_3098609, baseEnd_3098609] using wordTrace_append hprefix tailTrace_3098609
  have hstable : (prefixWord ++ tailWord_3098609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098609).length < 2 ^ (prefixWord ++ tailWord_3098609).sum := by decide
  have hdescent : baseEnd_3098609 < baseStart_3098609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098648 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_3098648 : Nat := 118140960795 + 3098648 * 2 ^ 59
def prefixEnd_3098648 : Nat := 4983230072969 + 3 ^ 40 * 3098648 * 2
def baseEnd_3098648 : Nat := 530365267697699253049861

theorem tailTrace_3098648 : CollatzResearch.WordTrace tailWord_3098648 prefixEnd_3098648 530365267697699253049861 := by
  unfold tailWord_3098648
  simp only [CollatzResearch.WordTrace]
  refine ⟨56508488639067488895596299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75344651518756651860795065 56508488639067488895596299)
  ·
    refine ⟨84762732958601233343394449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56508488639067488895596299 84762732958601233343394449)
    ·
      refine ⟨63572049718950925007545837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84762732958601233343394449 63572049718950925007545837)
      ·
        refine ⟨23839518644606596877829689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63572049718950925007545837 23839518644606596877829689)
        ·
          refine ⟨17879638983454947658372267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23839518644606596877829689 17879638983454947658372267)
          ·
            refine ⟨26819458475182421487558401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17879638983454947658372267 26819458475182421487558401)
            ·
              refine ⟨20114593856386816115668801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26819458475182421487558401 20114593856386816115668801)
              ·
                refine ⟨15085945392290112086751601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20114593856386816115668801 15085945392290112086751601)
                ·
                  refine ⟨11314459044217584065063701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15085945392290112086751601 11314459044217584065063701)
                  ·
                    refine ⟨530365267697699253049861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11314459044217584065063701 530365267697699253049861)
                    ·
                      rfl

theorem cell23_3098648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_3098648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098648 prefixEnd_3098648 := by exact prefixLift 3098648
  have htrace : WordTrace (prefixWord ++ tailWord_3098648) baseStart_3098648 baseEnd_3098648 := by
    simpa [prefixWord, tailWord_3098648, baseEnd_3098648] using wordTrace_append hprefix tailTrace_3098648
  have hstable : (prefixWord ++ tailWord_3098648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098648).length < 2 ^ (prefixWord ++ tailWord_3098648).sum := by decide
  have hdescent : baseEnd_3098648 < baseStart_3098648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098655 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 3, 4, 2]
def baseStart_3098655 : Nat := 118140960795 + 3098655 * 2 ^ 59
def prefixEnd_3098655 : Nat := 4983230072969 + 3 ^ 40 * 3098655 * 2
def baseEnd_3098655 : Nat := 1591099397457679231762051

theorem tailTrace_3098655 : CollatzResearch.WordTrace tailWord_3098655 prefixEnd_3098655 1591099397457679231762051 := by
  unfold tailWord_3098655
  simp only [CollatzResearch.WordTrace]
  refine ⟨113017232589109617986697419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75344821726073078657798279 113017232589109617986697419)
  ·
    refine ⟨169525848883664426980046129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113017232589109617986697419 169525848883664426980046129)
    ·
      refine ⟨127144386662748320235034597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169525848883664426980046129 127144386662748320235034597)
      ·
        refine ⟨23839572499265310044068987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127144386662748320235034597 23839572499265310044068987)
        ·
          refine ⟨35759358748897965066103481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23839572499265310044068987 35759358748897965066103481)
          ·
            refine ⟨26819519061673473799577611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35759358748897965066103481 26819519061673473799577611)
            ·
              refine ⟨40229278592510210699366417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26819519061673473799577611 40229278592510210699366417)
              ·
                refine ⟨30171958944382658024524813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40229278592510210699366417 30171958944382658024524813)
                ·
                  refine ⟨11314484604143496759196805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30171958944382658024524813 11314484604143496759196805)
                  ·
                    refine ⟨2121465863276905642349401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11314484604143496759196805 2121465863276905642349401)
                    ·
                      refine ⟨1591099397457679231762051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121465863276905642349401 1591099397457679231762051)
                      ·
                        rfl

theorem cell23_3098655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_3098655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098655 prefixEnd_3098655 := by exact prefixLift 3098655
  have htrace : WordTrace (prefixWord ++ tailWord_3098655) baseStart_3098655 baseEnd_3098655 := by
    simpa [prefixWord, tailWord_3098655, baseEnd_3098655] using wordTrace_append hprefix tailTrace_3098655
  have hstable : (prefixWord ++ tailWord_3098655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098655).length < 2 ^ (prefixWord ++ tailWord_3098655).sum := by decide
  have hdescent : baseEnd_3098655 < baseStart_3098655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098672 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 1, 4, 2]
def baseStart_3098672 : Nat := 118140960795 + 3098672 * 2 ^ 59
def prefixEnd_3098672 : Nat := 4983230072969 + 3 ^ 40 * 3098672 * 2
def baseEnd_3098672 : Nat := 1591108126628805665249473

theorem tailTrace_3098672 : CollatzResearch.WordTrace tailWord_3098672 prefixEnd_3098672 1591108126628805665249473 := by
  unfold tailWord_3098672
  simp only [CollatzResearch.WordTrace]
  refine ⟨56508926315024014945033135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75345235086698686593377513 56508926315024014945033135)
  ·
    refine ⟨84763389472536022417549703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56508926315024014945033135 84763389472536022417549703)
    ·
      refine ⟨127145084208804033626324555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84763389472536022417549703 127145084208804033626324555)
      ·
        refine ⟨190717626313206050439486833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127145084208804033626324555 190717626313206050439486833)
        ·
          refine ⟨143038219734904537829615125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190717626313206050439486833 143038219734904537829615125)
          ·
            refine ⟨6704916550073650210763209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143038219734904537829615125 6704916550073650210763209)
            ·
              refine ⟨5028687412555237658072407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6704916550073650210763209 5028687412555237658072407)
              ·
                refine ⟨7543031118832856487108611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028687412555237658072407 7543031118832856487108611)
                ·
                  refine ⟨11314546678249284730662917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543031118832856487108611 11314546678249284730662917)
                  ·
                    refine ⟨2121477502171740886999297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11314546678249284730662917 2121477502171740886999297)
                    ·
                      refine ⟨1591108126628805665249473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121477502171740886999297 1591108126628805665249473)
                      ·
                        rfl

theorem cell23_3098672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 4, 2].length) (baseStart_3098672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098672 prefixEnd_3098672 := by exact prefixLift 3098672
  have htrace : WordTrace (prefixWord ++ tailWord_3098672) baseStart_3098672 baseEnd_3098672 := by
    simpa [prefixWord, tailWord_3098672, baseEnd_3098672] using wordTrace_append hprefix tailTrace_3098672
  have hstable : (prefixWord ++ tailWord_3098672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098672).length < 2 ^ (prefixWord ++ tailWord_3098672).sum := by decide
  have hdescent : baseEnd_3098672 < baseStart_3098672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098745 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3098745 : Nat := 118140960795 + 3098745 * 2 ^ 59
def prefixEnd_3098745 : Nat := 4983230072969 + 3 ^ 40 * 3098745 * 2
def baseEnd_3098745 : Nat := 1591145610716583879636637

theorem tailTrace_3098745 : CollatzResearch.WordTrace tailWord_3098745 prefixEnd_3098745 1591145610716583879636637 := by
  unfold tailWord_3098745
  simp only [CollatzResearch.WordTrace]
  refine ⟨113020515158783563357473689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75347010105855708904982459 113020515158783563357473689)
  ·
    refine ⟨84765386369087672518105267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113020515158783563357473689 84765386369087672518105267)
    ·
      refine ⟨127148079553631508777157901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84765386369087672518105267 127148079553631508777157901)
      ·
        refine ⟨47680529832611815791434213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127148079553631508777157901 47680529832611815791434213)
        ·
          refine ⟨8940099343614715460893915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47680529832611815791434213 8940099343614715460893915)
          ·
            refine ⟨13410149015422073191340873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8940099343614715460893915 13410149015422073191340873)
            ·
              refine ⟨10057611761566554893505655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13410149015422073191340873 10057611761566554893505655)
              ·
                refine ⟨15086417642349832340258483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10057611761566554893505655 15086417642349832340258483)
                ·
                  refine ⟨22629626463524748510387725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15086417642349832340258483 22629626463524748510387725)
                  ·
                    refine ⟨8486109923821780691395397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22629626463524748510387725 8486109923821780691395397)
                    ·
                      refine ⟨1591145610716583879636637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8486109923821780691395397 1591145610716583879636637)
                      ·
                        rfl

theorem cell23_3098745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3098745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098745 prefixEnd_3098745 := by exact prefixLift 3098745
  have htrace : WordTrace (prefixWord ++ tailWord_3098745) baseStart_3098745 baseEnd_3098745 := by
    simpa [prefixWord, tailWord_3098745, baseEnd_3098745] using wordTrace_append hprefix tailTrace_3098745
  have hstable : (prefixWord ++ tailWord_3098745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098745).length < 2 ^ (prefixWord ++ tailWord_3098745).sum := by decide
  have hdescent : baseEnd_3098745 < baseStart_3098745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098762 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3098762 : Nat := 118140960795 + 3098762 * 2 ^ 59
def prefixEnd_3098762 : Nat := 4983230072969 + 3 ^ 40 * 3098762 * 2
def baseEnd_3098762 : Nat := 1591154339887710313124059

theorem tailTrace_3098762 : CollatzResearch.WordTrace tailWord_3098762 prefixEnd_3098762 1591154339887710313124059 := by
  unfold tailWord_3098762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28255283799930493815210635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75347423466481316840561693 28255283799930493815210635)
  ·
    refine ⟨42382925699895740722815953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28255283799930493815210635 42382925699895740722815953)
    ·
      refine ⟨31787194274921805542111965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42382925699895740722815953 31787194274921805542111965)
      ·
        refine ⟨11920197853095677078291987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31787194274921805542111965 11920197853095677078291987)
        ·
          refine ⟨17880296779643515617437981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11920197853095677078291987 17880296779643515617437981)
          ·
            refine ⟨6705111292366318356539243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17880296779643515617437981 6705111292366318356539243)
            ·
              refine ⟨10057666938549477534808865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6705111292366318356539243 10057666938549477534808865)
              ·
                refine ⟨7543250203912108151106649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10057666938549477534808865 7543250203912108151106649)
                ·
                  refine ⟨5657437652934081113329987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543250203912108151106649 5657437652934081113329987)
                  ·
                    refine ⟨8486156479401121669994981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657437652934081113329987 8486156479401121669994981)
                    ·
                      refine ⟨1591154339887710313124059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8486156479401121669994981 1591154339887710313124059)
                      ·
                        rfl

theorem cell23_3098762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3098762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098762 prefixEnd_3098762 := by exact prefixLift 3098762
  have htrace : WordTrace (prefixWord ++ tailWord_3098762) baseStart_3098762 baseEnd_3098762 := by
    simpa [prefixWord, tailWord_3098762, baseEnd_3098762] using wordTrace_append hprefix tailTrace_3098762
  have hstable : (prefixWord ++ tailWord_3098762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098762).length < 2 ^ (prefixWord ++ tailWord_3098762).sum := by decide
  have hdescent : baseEnd_3098762 < baseStart_3098762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098768 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 8]
def baseStart_3098768 : Nat := 118140960795 + 3098768 * 2 ^ 59
def prefixEnd_3098768 : Nat := 4983230072969 + 3 ^ 40 * 3098768 * 2
def baseEnd_3098768 : Nat := 176795268974626365516559

theorem tailTrace_3098768 : CollatzResearch.WordTrace tailWord_3098768 prefixEnd_3098768 176795268974626365516559 := by
  unfold tailWord_3098768
  simp only [CollatzResearch.WordTrace]
  refine ⟨56510677018850119142780479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75347569358466825523707305 56510677018850119142780479)
  ·
    refine ⟨84766015528275178714170719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56510677018850119142780479 84766015528275178714170719)
    ·
      refine ⟨127149023292412768071256079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84766015528275178714170719 127149023292412768071256079)
      ·
        refine ⟨190723534938619152106884119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127149023292412768071256079 190723534938619152106884119)
        ·
          refine ⟨286085302407928728160326179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190723534938619152106884119 286085302407928728160326179)
          ·
            refine ⟨429127953611893092240489269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286085302407928728160326179 429127953611893092240489269)
            ·
              refine ⟨40230745651114977397545869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 429127953611893092240489269 40230745651114977397545869)
              ·
                refine ⟨15086529619168116524079701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40230745651114977397545869 15086529619168116524079701)
                ·
                  refine ⟨176795268974626365516559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15086529619168116524079701 176795268974626365516559)
                  ·
                    rfl

theorem cell23_3098768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_3098768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098768 prefixEnd_3098768 := by exact prefixLift 3098768
  have htrace : WordTrace (prefixWord ++ tailWord_3098768) baseStart_3098768 baseEnd_3098768 := by
    simpa [prefixWord, tailWord_3098768, baseEnd_3098768] using wordTrace_append hprefix tailTrace_3098768
  have hstable : (prefixWord ++ tailWord_3098768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098768).length < 2 ^ (prefixWord ++ tailWord_3098768).sum := by decide
  have hdescent : baseEnd_3098768 < baseStart_3098768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098850 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3098850 : Nat := 118140960795 + 3098850 * 2 ^ 59
def prefixEnd_3098850 : Nat := 4983230072969 + 3 ^ 40 * 3098850 * 2
def baseEnd_3098850 : Nat := 1591199526185305968823655

theorem tailTrace_3098850 : CollatzResearch.WordTrace tailWord_3098850 prefixEnd_3098850 1591199526185305968823655 := by
  unfold tailWord_3098850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256086205850791572511501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75349563215602110860030669 28256086205850791572511501)
  ·
    refine ⟨10596032327194046839691813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28256086205850791572511501 10596032327194046839691813)
    ·
      refine ⟨1986756061348883782442215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10596032327194046839691813 1986756061348883782442215)
      ·
        refine ⟨2980134092023325673663323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986756061348883782442215 2980134092023325673663323)
        ·
          refine ⟨4470201138034988510494985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980134092023325673663323 4470201138034988510494985)
          ·
            refine ⟨3352650853526241382871239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4470201138034988510494985 3352650853526241382871239)
            ·
              refine ⟨5028976280289362074306859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352650853526241382871239 5028976280289362074306859)
              ·
                refine ⟨7543464420434043111460289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028976280289362074306859 7543464420434043111460289)
                ·
                  refine ⟨5657598315325532333595217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543464420434043111460289 5657598315325532333595217)
                  ·
                    refine ⟨4243198736494149250196413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5657598315325532333595217 4243198736494149250196413)
                    ·
                      refine ⟨1591199526185305968823655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243198736494149250196413 1591199526185305968823655)
                      ·
                        rfl

theorem cell23_3098850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3098850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098850 prefixEnd_3098850 := by exact prefixLift 3098850
  have htrace : WordTrace (prefixWord ++ tailWord_3098850) baseStart_3098850 baseEnd_3098850 := by
    simpa [prefixWord, tailWord_3098850, baseEnd_3098850] using wordTrace_append hprefix tailTrace_3098850
  have hstable : (prefixWord ++ tailWord_3098850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098850).length < 2 ^ (prefixWord ++ tailWord_3098850).sum := by decide
  have hdescent : baseEnd_3098850 < baseStart_3098850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098852 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_3098852 : Nat := 118140960795 + 3098852 * 2 ^ 59
def prefixEnd_3098852 : Nat := 4983230072969 + 3 ^ 40 * 3098852 * 2
def baseEnd_3098852 : Nat := 1591200553146614960998645

theorem tailTrace_3098852 : CollatzResearch.WordTrace tailWord_3098852 prefixEnd_3098852 1591200553146614960998645 := by
  unfold tailWord_3098852
  simp only [CollatzResearch.WordTrace]
  refine ⟨56512208884697960315809405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75349611846263947087745873 56512208884697960315809405)
  ·
    refine ⟨21192078331761735118428527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56512208884697960315809405 21192078331761735118428527)
    ·
      refine ⟨31788117497642602677642791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21192078331761735118428527 31788117497642602677642791)
      ·
        refine ⟨47682176246463904016464187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31788117497642602677642791 47682176246463904016464187)
        ·
          refine ⟨71523264369695856024696281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47682176246463904016464187 71523264369695856024696281)
          ·
            refine ⟨53642448277271892018522211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71523264369695856024696281 53642448277271892018522211)
            ·
              refine ⟨80463672415907838027783317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53642448277271892018522211 80463672415907838027783317)
              ·
                refine ⟨3771734644495679907552343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80463672415907838027783317 3771734644495679907552343)
                ·
                  refine ⟨5657601966743519861328515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771734644495679907552343 5657601966743519861328515)
                  ·
                    refine ⟨8486402950115279791992773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657601966743519861328515 8486402950115279791992773)
                    ·
                      refine ⟨1591200553146614960998645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8486402950115279791992773 1591200553146614960998645)
                      ·
                        rfl

theorem cell23_3098852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_3098852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098852 prefixEnd_3098852 := by exact prefixLift 3098852
  have htrace : WordTrace (prefixWord ++ tailWord_3098852) baseStart_3098852 baseEnd_3098852 := by
    simpa [prefixWord, tailWord_3098852, baseEnd_3098852] using wordTrace_append hprefix tailTrace_3098852
  have hstable : (prefixWord ++ tailWord_3098852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098852).length < 2 ^ (prefixWord ++ tailWord_3098852).sum := by decide
  have hdescent : baseEnd_3098852 < baseStart_3098852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098856 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_3098856 : Nat := 118140960795 + 3098856 * 2 ^ 59
def prefixEnd_3098856 : Nat := 4983230072969 + 3 ^ 40 * 3098856 * 2
def baseEnd_3098856 : Nat := 1591202607069232945348627

theorem tailTrace_3098856 : CollatzResearch.WordTrace tailWord_3098856 prefixEnd_3098856 1591202607069232945348627 := by
  unfold tailWord_3098856
  simp only [CollatzResearch.WordTrace]
  refine ⟨56512281830690714657382211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75349709107587619543176281 56512281830690714657382211)
  ·
    refine ⟨84768422746036071986073317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56512281830690714657382211 84768422746036071986073317)
    ·
      refine ⟨15894079264881763497388747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84768422746036071986073317 15894079264881763497388747)
      ·
        refine ⟨23841118897322645246083121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894079264881763497388747 23841118897322645246083121)
        ·
          refine ⟨17880839172991983934562341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23841118897322645246083121 17880839172991983934562341)
          ·
            refine ⟨3352657344935996987730439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17880839172991983934562341 3352657344935996987730439)
            ·
              refine ⟨5028986017403995481595659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352657344935996987730439 5028986017403995481595659)
              ·
                refine ⟨7543479026105993222393489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028986017403995481595659 7543479026105993222393489)
                ·
                  refine ⟨5657609269579494916795117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543479026105993222393489 5657609269579494916795117)
                  ·
                    refine ⟨2121603476092310593798169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5657609269579494916795117 2121603476092310593798169)
                    ·
                      refine ⟨1591202607069232945348627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121603476092310593798169 1591202607069232945348627)
                      ·
                        rfl

theorem cell23_3098856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_3098856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098856 prefixEnd_3098856 := by exact prefixLift 3098856
  have htrace : WordTrace (prefixWord ++ tailWord_3098856) baseStart_3098856 baseEnd_3098856 := by
    simpa [prefixWord, tailWord_3098856, baseEnd_3098856] using wordTrace_append hprefix tailTrace_3098856
  have hstable : (prefixWord ++ tailWord_3098856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098856).length < 2 ^ (prefixWord ++ tailWord_3098856).sum := by decide
  have hdescent : baseEnd_3098856 < baseStart_3098856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098862 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3098862 : Nat := 118140960795 + 3098862 * 2 ^ 59
def prefixEnd_3098862 : Nat := 4983230072969 + 3 ^ 40 * 3098862 * 2
def baseEnd_3098862 : Nat := 530401895984386640624533

theorem tailTrace_3098862 : CollatzResearch.WordTrace tailWord_3098862 prefixEnd_3098862 530401895984386640624533 := by
  unfold tailWord_3098862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128097812419961542435355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75349854999573128226321893 14128097812419961542435355)
  ·
    refine ⟨21192146718629942313653033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14128097812419961542435355 21192146718629942313653033)
    ·
      refine ⟨15894110038972456735239775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21192146718629942313653033 15894110038972456735239775)
      ·
        refine ⟨23841165058458685102859663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894110038972456735239775 23841165058458685102859663)
        ·
          refine ⟨35761747587688027654289495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23841165058458685102859663 35761747587688027654289495)
          ·
            refine ⟨53642621381532041481434243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35761747587688027654289495 53642621381532041481434243)
            ·
              refine ⟨80463932072298062222151365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53642621381532041481434243 80463932072298062222151365)
              ·
                refine ⟨15086987263555886666653381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80463932072298062222151365 15086987263555886666653381)
                ·
                  refine ⟨2828810111916728749997509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15086987263555886666653381 2828810111916728749997509)
                  ·
                    refine ⟨530401895984386640624533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828810111916728749997509 530401895984386640624533)
                    ·
                      rfl

theorem cell23_3098862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3098862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098862 prefixEnd_3098862 := by exact prefixLift 3098862
  have htrace : WordTrace (prefixWord ++ tailWord_3098862) baseStart_3098862 baseEnd_3098862 := by
    simpa [prefixWord, tailWord_3098862, baseEnd_3098862] using wordTrace_append hprefix tailTrace_3098862
  have hstable : (prefixWord ++ tailWord_3098862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098862).length < 2 ^ (prefixWord ++ tailWord_3098862).sum := by decide
  have hdescent : baseEnd_3098862 < baseStart_3098862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098866 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3098866 : Nat := 118140960795 + 3098866 * 2 ^ 59
def prefixEnd_3098866 : Nat := 4983230072969 + 3 ^ 40 * 3098866 * 2
def baseEnd_3098866 : Nat := 530402580625259302074527

theorem tailTrace_3098866 : CollatzResearch.WordTrace tailWord_3098866 prefixEnd_3098866 530402580625259302074527 := by
  unfold tailWord_3098866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256232097836300255657113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75349952260896800681752301 28256232097836300255657113)
  ·
    refine ⟨21192174073377225191742835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28256232097836300255657113 21192174073377225191742835)
    ·
      refine ⟨31788261110065837787614253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21192174073377225191742835 31788261110065837787614253)
      ·
        refine ⟨11920597916274689170355345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31788261110065837787614253 11920597916274689170355345)
        ·
          refine ⟨8940448437206016877766509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11920597916274689170355345 8940448437206016877766509)
          ·
            refine ⟨3352668163952256329162441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8940448437206016877766509 3352668163952256329162441)
            ·
              refine ⟨2514501122964192246871831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352668163952256329162441 2514501122964192246871831)
              ·
                refine ⟨3771751684446288370307747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514501122964192246871831 3771751684446288370307747)
                ·
                  refine ⟨5657627526669432555461621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771751684446288370307747 5657627526669432555461621)
                  ·
                    refine ⟨530402580625259302074527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5657627526669432555461621 530402580625259302074527)
                    ·
                      rfl

theorem cell23_3098866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3098866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098866 prefixEnd_3098866 := by exact prefixLift 3098866
  have htrace : WordTrace (prefixWord ++ tailWord_3098866) baseStart_3098866 baseEnd_3098866 := by
    simpa [prefixWord, tailWord_3098866, baseEnd_3098866] using wordTrace_append hprefix tailTrace_3098866
  have hstable : (prefixWord ++ tailWord_3098866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098866).length < 2 ^ (prefixWord ++ tailWord_3098866).sum := by decide
  have hdescent : baseEnd_3098866 < baseStart_3098866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098906 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_3098906 : Nat := 118140960795 + 3098906 * 2 ^ 59
def prefixEnd_3098906 : Nat := 4983230072969 + 3 ^ 40 * 3098906 * 2
def baseEnd_3098906 : Nat := 1591228281101957749723397

theorem tailTrace_3098906 : CollatzResearch.WordTrace tailWord_3098906 prefixEnd_3098906 1591228281101957749723397 := by
  unfold tailWord_3098906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256596827800071963521143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75350924874133525236056381 28256596827800071963521143)
  ·
    refine ⟨42384895241700107945281715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28256596827800071963521143 42384895241700107945281715)
    ·
      refine ⟨63577342862550161917922573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42384895241700107945281715 63577342862550161917922573)
      ·
        refine ⟨23841503573456310719220965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63577342862550161917922573 23841503573456310719220965)
        ·
          refine ⟨4470281920023058259853931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23841503573456310719220965 4470281920023058259853931)
          ·
            refine ⟨6705422880034587389780897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470281920023058259853931 6705422880034587389780897)
            ·
              refine ⟨5029067160025940542335673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705422880034587389780897 5029067160025940542335673)
              ·
                refine ⟨3771800370019455406751755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029067160025940542335673 3771800370019455406751755)
                ·
                  refine ⟨5657700555029183110127633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771800370019455406751755 5657700555029183110127633)
                  ·
                    refine ⟨4243275416271887332595725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5657700555029183110127633 4243275416271887332595725)
                    ·
                      refine ⟨1591228281101957749723397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243275416271887332595725 1591228281101957749723397)
                      ·
                        rfl

theorem cell23_3098906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_3098906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098906 prefixEnd_3098906 := by exact prefixLift 3098906
  have htrace : WordTrace (prefixWord ++ tailWord_3098906) baseStart_3098906 baseEnd_3098906 := by
    simpa [prefixWord, tailWord_3098906, baseEnd_3098906] using wordTrace_append hprefix tailTrace_3098906
  have hstable : (prefixWord ++ tailWord_3098906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098906).length < 2 ^ (prefixWord ++ tailWord_3098906).sum := by decide
  have hdescent : baseEnd_3098906 < baseStart_3098906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098915 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3098915 : Nat := 118140960795 + 3098915 * 2 ^ 59
def prefixEnd_3098915 : Nat := 4983230072969 + 3 ^ 40 * 3098915 * 2
def baseEnd_3098915 : Nat := 1591232902427848214510855

theorem tailTrace_3098915 : CollatzResearch.WordTrace tailWord_3098915 prefixEnd_3098915 1591232902427848214510855 := by
  unfold tailWord_3098915
  simp only [CollatzResearch.WordTrace]
  refine ⟨113026715568167682391162199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75351143712111788260774799 113026715568167682391162199)
  ·
    refine ⟨169540073352251523586743299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113026715568167682391162199 169540073352251523586743299)
    ·
      refine ⟨254310110028377285380114949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169540073352251523586743299 254310110028377285380114949)
      ·
        refine ⟨47683145630320741008771553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254310110028377285380114949 47683145630320741008771553)
        ·
          refine ⟨35762359222740555756578665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47683145630320741008771553 35762359222740555756578665)
          ·
            refine ⟨26821769417055416817433999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35762359222740555756578665 26821769417055416817433999)
            ·
              refine ⟨40232654125583125226150999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26821769417055416817433999 40232654125583125226150999)
              ·
                refine ⟨60348981188374687839226499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40232654125583125226150999 60348981188374687839226499)
                ·
                  refine ⟨90523471782562031758839749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60348981188374687839226499 90523471782562031758839749)
                  ·
                    refine ⟨16973150959230380954782453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90523471782562031758839749 16973150959230380954782453)
                    ·
                      refine ⟨1591232902427848214510855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16973150959230380954782453 1591232902427848214510855)
                      ·
                        rfl

theorem cell23_3098915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3098915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098915 prefixEnd_3098915 := by exact prefixLift 3098915
  have htrace : WordTrace (prefixWord ++ tailWord_3098915) baseStart_3098915 baseEnd_3098915 := by
    simpa [prefixWord, tailWord_3098915, baseEnd_3098915] using wordTrace_append hprefix tailTrace_3098915
  have hstable : (prefixWord ++ tailWord_3098915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098915).length < 2 ^ (prefixWord ++ tailWord_3098915).sum := by decide
  have hdescent : baseEnd_3098915 < baseStart_3098915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098926 : List Nat := [4, 1, 3, 3, 2, 1, 9]
def baseStart_3098926 : Nat := 118140960795 + 3098926 * 2 ^ 59
def prefixEnd_3098926 : Nat := 4983230072969 + 3 ^ 40 * 3098926 * 2
def baseEnd_3098926 : Nat := 19644920379198119400905

theorem tailTrace_3098926 : CollatzResearch.WordTrace tailWord_3098926 prefixEnd_3098926 19644920379198119400905 := by
  unfold tailWord_3098926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128389596390978908726579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75351411180751887513208421 14128389596390978908726579)
  ·
    refine ⟨21192584394586468363089869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14128389596390978908726579 21192584394586468363089869)
    ·
      refine ⟨7947219147969925636158701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21192584394586468363089869 7947219147969925636158701)
      ·
        refine ⟨2980207180488722113559513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7947219147969925636158701 2980207180488722113559513)
        ·
          refine ⟨2235155385366541585169635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980207180488722113559513 2235155385366541585169635)
          ·
            refine ⟨3352733078049812377754453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235155385366541585169635 3352733078049812377754453)
            ·
              refine ⟨19644920379198119400905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3352733078049812377754453 19644920379198119400905)
              ·
                rfl

theorem cell23_3098926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 9].length) (baseStart_3098926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098926 prefixEnd_3098926 := by exact prefixLift 3098926
  have htrace : WordTrace (prefixWord ++ tailWord_3098926) baseStart_3098926 baseEnd_3098926 := by
    simpa [prefixWord, tailWord_3098926, baseEnd_3098926] using wordTrace_append hprefix tailTrace_3098926
  have hstable : (prefixWord ++ tailWord_3098926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098926).length < 2 ^ (prefixWord ++ tailWord_3098926).sum := by decide
  have hdescent : baseEnd_3098926 < baseStart_3098926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098935 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 4, 6]
def baseStart_3098935 : Nat := 118140960795 + 3098935 * 2 ^ 59
def prefixEnd_3098935 : Nat := 4983230072969 + 3 ^ 40 * 3098935 * 2
def baseEnd_3098935 : Nat := 530414390680312712086921

theorem tailTrace_3098935 : CollatzResearch.WordTrace tailWord_3098935 prefixEnd_3098935 530414390680312712086921 := by
  unfold tailWord_3098935
  simp only [CollatzResearch.WordTrace]
  refine ⟨113027445028095225806890259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75351630018730150537926839 113027445028095225806890259)
  ·
    refine ⟨169541167542142838710335389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113027445028095225806890259 169541167542142838710335389)
    ·
      refine ⟨63577937828303564516375771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169541167542142838710335389 63577937828303564516375771)
      ·
        refine ⟨95366906742455346774563657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63577937828303564516375771 95366906742455346774563657)
        ·
          refine ⟨71525180056841510080922743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95366906742455346774563657 71525180056841510080922743)
          ·
            refine ⟨107287770085262265121384115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71525180056841510080922743 107287770085262265121384115)
            ·
              refine ⟨160931655127893397682076173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107287770085262265121384115 160931655127893397682076173)
              ·
                refine ⟨60349370672960024130778565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160931655127893397682076173 60349370672960024130778565)
                ·
                  refine ⟨11315507001180004524520981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60349370672960024130778565 11315507001180004524520981)
                  ·
                    refine ⟨530414390680312712086921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11315507001180004524520981 530414390680312712086921)
                    ·
                      rfl

theorem cell23_3098935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_3098935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098935 prefixEnd_3098935 := by exact prefixLift 3098935
  have htrace : WordTrace (prefixWord ++ tailWord_3098935) baseStart_3098935 baseEnd_3098935 := by
    simpa [prefixWord, tailWord_3098935, baseEnd_3098935] using wordTrace_append hprefix tailTrace_3098935
  have hstable : (prefixWord ++ tailWord_3098935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098935).length < 2 ^ (prefixWord ++ tailWord_3098935).sum := by decide
  have hdescent : baseEnd_3098935 < baseStart_3098935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098959 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 6, 2, 2]
def baseStart_3098959 : Nat := 118140960795 + 3098959 * 2 ^ 59
def prefixEnd_3098959 : Nat := 4983230072969 + 3 ^ 40 * 3098959 * 2
def baseEnd_3098959 : Nat := 1591255495576646042360653

theorem tailTrace_3098959 : CollatzResearch.WordTrace tailWord_3098959 prefixEnd_3098959 1591255495576646042360653 := by
  unfold tailWord_3098959
  simp only [CollatzResearch.WordTrace]
  refine ⟨113028320380008277905763931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75352213586672185270509287 113028320380008277905763931)
  ·
    refine ⟨169542480570012416858645897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113028320380008277905763931 169542480570012416858645897)
    ·
      refine ⟨127156860427509312643984423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169542480570012416858645897 127156860427509312643984423)
      ·
        refine ⟨190735290641263968965976635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127156860427509312643984423 190735290641263968965976635)
        ·
          refine ⟨286102935961895953448964953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190735290641263968965976635 286102935961895953448964953)
          ·
            refine ⟨214577201971421965086723715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286102935961895953448964953 214577201971421965086723715)
            ·
              refine ⟨321865802957132947630085573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214577201971421965086723715 321865802957132947630085573)
              ·
                refine ⟨60349838054462427680641045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321865802957132947630085573 60349838054462427680641045)
                ·
                  refine ⟨2828898658802926297530049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60349838054462427680641045 2828898658802926297530049)
                  ·
                    refine ⟨2121673994102194723147537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828898658802926297530049 2121673994102194723147537)
                    ·
                      refine ⟨1591255495576646042360653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121673994102194723147537 1591255495576646042360653)
                      ·
                        rfl

theorem cell23_3098959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 2, 2].length) (baseStart_3098959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098959 prefixEnd_3098959 := by exact prefixLift 3098959
  have htrace : WordTrace (prefixWord ++ tailWord_3098959) baseStart_3098959 baseEnd_3098959 := by
    simpa [prefixWord, tailWord_3098959, baseEnd_3098959] using wordTrace_append hprefix tailTrace_3098959
  have hstable : (prefixWord ++ tailWord_3098959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098959).length < 2 ^ (prefixWord ++ tailWord_3098959).sum := by decide
  have hdescent : baseEnd_3098959 < baseStart_3098959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098962 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3098962 : Nat := 118140960795 + 3098962 * 2 ^ 59
def prefixEnd_3098962 : Nat := 4983230072969 + 3 ^ 40 * 3098962 * 2
def baseEnd_3098962 : Nat := 1591257036018609530623139

theorem tailTrace_3098962 : CollatzResearch.WordTrace tailWord_3098962 prefixEnd_3098962 1591257036018609530623139 := by
  unfold tailWord_3098962
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257107449749352354530785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75352286532664939612082093 28257107449749352354530785)
  ·
    refine ⟨21192830587312014265898089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28257107449749352354530785 21192830587312014265898089)
    ·
      refine ⟨15894622940484010699423567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21192830587312014265898089 15894622940484010699423567)
      ·
        refine ⟨23841934410726016049135351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894622940484010699423567 23841934410726016049135351)
        ·
          refine ⟨35762901616089024073703027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23841934410726016049135351 35762901616089024073703027)
          ·
            refine ⟨53644352424133536110554541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35762901616089024073703027 53644352424133536110554541)
            ·
              refine ⟨20116632159050076041457953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53644352424133536110554541 20116632159050076041457953)
              ·
                refine ⟨15087474119287557031093465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20116632159050076041457953 15087474119287557031093465)
                ·
                  refine ⟨11315605589465667773320099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15087474119287557031093465 11315605589465667773320099)
                  ·
                    refine ⟨16973408384198501659980149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11315605589465667773320099 16973408384198501659980149)
                    ·
                      refine ⟨1591257036018609530623139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16973408384198501659980149 1591257036018609530623139)
                      ·
                        rfl

theorem cell23_3098962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3098962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098962 prefixEnd_3098962 := by exact prefixLift 3098962
  have htrace : WordTrace (prefixWord ++ tailWord_3098962) baseStart_3098962 baseEnd_3098962 := by
    simpa [prefixWord, tailWord_3098962, baseEnd_3098962] using wordTrace_append hprefix tailTrace_3098962
  have hstable : (prefixWord ++ tailWord_3098962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098962).length < 2 ^ (prefixWord ++ tailWord_3098962).sum := by decide
  have hdescent : baseEnd_3098962 < baseStart_3098962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098974 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3098974 : Nat := 118140960795 + 3098974 * 2 ^ 59
def prefixEnd_3098974 : Nat := 4983230072969 + 3 ^ 40 * 3098974 * 2
def baseEnd_3098974 : Nat := 1591263197786463483673085

theorem tailTrace_3098974 : CollatzResearch.WordTrace tailWord_3098974 prefixEnd_3098974 1591263197786463483673085 := by
  unfold tailWord_3098974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128608434369241933444997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75352578316635956978373317 14128608434369241933444997)
  ·
    refine ⟨2649114081444232862520937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14128608434369241933444997 2649114081444232862520937)
    ·
      refine ⟨1986835561083174646890703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2649114081444232862520937 1986835561083174646890703)
      ·
        refine ⟨2980253341624761970336055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986835561083174646890703 2980253341624761970336055)
        ·
          refine ⟨4470380012437142955504083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980253341624761970336055 4470380012437142955504083)
          ·
            refine ⟨6705570018655714433256125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470380012437142955504083 6705570018655714433256125)
            ·
              refine ⟨2514588756995892912471047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6705570018655714433256125 2514588756995892912471047)
              ·
                refine ⟨3771883135493839368706571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514588756995892912471047 3771883135493839368706571)
                ·
                  refine ⟨5657824703240759053059857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771883135493839368706571 5657824703240759053059857)
                  ·
                    refine ⟨4243368527430569289794893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5657824703240759053059857 4243368527430569289794893)
                    ·
                      refine ⟨1591263197786463483673085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243368527430569289794893 1591263197786463483673085)
                      ·
                        rfl

theorem cell23_3098974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3098974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098974 prefixEnd_3098974 := by exact prefixLift 3098974
  have htrace : WordTrace (prefixWord ++ tailWord_3098974) baseStart_3098974 baseEnd_3098974 := by
    simpa [prefixWord, tailWord_3098974, baseEnd_3098974] using wordTrace_append hprefix tailTrace_3098974
  have hstable : (prefixWord ++ tailWord_3098974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098974).length < 2 ^ (prefixWord ++ tailWord_3098974).sum := by decide
  have hdescent : baseEnd_3098974 < baseStart_3098974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098976 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 1, 4, 2]
def baseStart_3098976 : Nat := 118140960795 + 3098976 * 2 ^ 59
def prefixEnd_3098976 : Nat := 4983230072969 + 3 ^ 40 * 3098976 * 2
def baseEnd_3098976 : Nat := 1591264224747772475848075

theorem tailTrace_3098976 : CollatzResearch.WordTrace tailWord_3098976 prefixEnd_3098976 1591264224747772475848075 := by
  unfold tailWord_3098976
  simp only [CollatzResearch.WordTrace]
  refine ⟨56514470210473344904566391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75352626947297793206088521 56514470210473344904566391)
  ·
    refine ⟨84771705315710017356849587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56514470210473344904566391 84771705315710017356849587)
    ·
      refine ⟨127157557973565026035274381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84771705315710017356849587 127157557973565026035274381)
      ·
        refine ⟨47684084240086884763227893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127157557973565026035274381 47684084240086884763227893)
        ·
          refine ⟨4470382897508145446552615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47684084240086884763227893 4470382897508145446552615)
          ·
            refine ⟨6705574346262218169828923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470382897508145446552615 6705574346262218169828923)
            ·
              refine ⟨10058361519393327254743385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6705574346262218169828923 10058361519393327254743385)
              ·
                refine ⟨7543771139544995441057539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10058361519393327254743385 7543771139544995441057539)
                ·
                  refine ⟨11315656709317493161586309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543771139544995441057539 11315656709317493161586309)
                  ·
                    refine ⟨2121685632997029967797433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11315656709317493161586309 2121685632997029967797433)
                    ·
                      refine ⟨1591264224747772475848075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121685632997029967797433 1591264224747772475848075)
                      ·
                        rfl

theorem cell23_3098976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_3098976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3098976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3098976 prefixEnd_3098976 := by exact prefixLift 3098976
  have htrace : WordTrace (prefixWord ++ tailWord_3098976) baseStart_3098976 baseEnd_3098976 := by
    simpa [prefixWord, tailWord_3098976, baseEnd_3098976] using wordTrace_append hprefix tailTrace_3098976
  have hstable : (prefixWord ++ tailWord_3098976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098976).length < 2 ^ (prefixWord ++ tailWord_3098976).sum := by decide
  have hdescent : baseEnd_3098976 < baseStart_3098976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099009 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3099009 : Nat := 118140960795 + 3099009 * 2 ^ 59
def prefixEnd_3099009 : Nat := 4983230072969 + 3 ^ 40 * 3099009 * 2
def baseEnd_3099009 : Nat := 1591281169609370846735423

theorem tailTrace_3099009 : CollatzResearch.WordTrace tailWord_3099009 prefixEnd_3099009 1591281169609370846735423 := by
  unfold tailWord_3099009
  simp only [CollatzResearch.WordTrace]
  refine ⟨113030144029827136445084081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75353429353218090963389387 113030144029827136445084081)
  ·
    refine ⟨84772608022370352333813061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113030144029827136445084081 84772608022370352333813061)
    ·
      refine ⟨15894864004194441062589949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84772608022370352333813061 15894864004194441062589949)
      ·
        refine ⟨5960574001572915398471231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15894864004194441062589949 5960574001572915398471231)
        ·
          refine ⟨8940861002359373097706847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960574001572915398471231 8940861002359373097706847)
          ·
            refine ⟨13411291503539059646560271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8940861002359373097706847 13411291503539059646560271)
            ·
              refine ⟨20116937255308589469840407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411291503539059646560271 20116937255308589469840407)
              ·
                refine ⟨30175405882962884204760611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20116937255308589469840407 30175405882962884204760611)
                ·
                  refine ⟨45263108824444326307140917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30175405882962884204760611 45263108824444326307140917)
                  ·
                    refine ⟨4243416452291655591294461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45263108824444326307140917 4243416452291655591294461)
                    ·
                      refine ⟨1591281169609370846735423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243416452291655591294461 1591281169609370846735423)
                      ·
                        rfl

theorem cell23_3099009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3099009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099009 prefixEnd_3099009 := by exact prefixLift 3099009
  have htrace : WordTrace (prefixWord ++ tailWord_3099009) baseStart_3099009 baseEnd_3099009 := by
    simpa [prefixWord, tailWord_3099009, baseEnd_3099009] using wordTrace_append hprefix tailTrace_3099009
  have hstable : (prefixWord ++ tailWord_3099009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099009).length < 2 ^ (prefixWord ++ tailWord_3099009).sum := by decide
  have hdescent : baseEnd_3099009 < baseStart_3099009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099010 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3099010 : Nat := 118140960795 + 3099010 * 2 ^ 59
def prefixEnd_3099010 : Nat := 4983230072969 + 3 ^ 40 * 3099010 * 2
def baseEnd_3099010 : Nat := 1591281683090025342822919

theorem tailTrace_3099010 : CollatzResearch.WordTrace tailWord_3099010 prefixEnd_3099010 1591281683090025342822919 := by
  unfold tailWord_3099010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257545125705878403967621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75353453668549009077246989 28257545125705878403967621)
  ·
    refine ⟨5298289711069852200743929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28257545125705878403967621 5298289711069852200743929)
    ·
      refine ⟨3973717283302389150557947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5298289711069852200743929 3973717283302389150557947)
      ·
        refine ⟨5960575924953583725836921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3973717283302389150557947 5960575924953583725836921)
        ·
          refine ⟨4470431943715187794377691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960575924953583725836921 4470431943715187794377691)
          ·
            refine ⟨6705647915572781691566537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470431943715187794377691 6705647915572781691566537)
            ·
              refine ⟨5029235936679586268674903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705647915572781691566537 5029235936679586268674903)
              ·
                refine ⟨7543853905019379403012355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029235936679586268674903 7543853905019379403012355)
                ·
                  refine ⟨11315780857529069104518533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543853905019379403012355 11315780857529069104518533)
                  ·
                    refine ⟨2121708910786700457097225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11315780857529069104518533 2121708910786700457097225)
                    ·
                      refine ⟨1591281683090025342822919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121708910786700457097225 1591281683090025342822919)
                      ·
                        rfl

theorem cell23_3099010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3099010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099010 prefixEnd_3099010 := by exact prefixLift 3099010
  have htrace : WordTrace (prefixWord ++ tailWord_3099010) baseStart_3099010 baseEnd_3099010 := by
    simpa [prefixWord, tailWord_3099010, baseEnd_3099010] using wordTrace_append hprefix tailTrace_3099010
  have hstable : (prefixWord ++ tailWord_3099010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099010).length < 2 ^ (prefixWord ++ tailWord_3099010).sum := by decide
  have hdescent : baseEnd_3099010 < baseStart_3099010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099012 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3099012 : Nat := 118140960795 + 3099012 * 2 ^ 59
def prefixEnd_3099012 : Nat := 4983230072969 + 3 ^ 40 * 3099012 * 2
def baseEnd_3099012 : Nat := 530427570017111444999303

theorem tailTrace_3099012 : CollatzResearch.WordTrace tailWord_3099012 prefixEnd_3099012 530427570017111444999303 := by
  unfold tailWord_3099012
  simp only [CollatzResearch.WordTrace]
  refine ⟨56515126724408133978721645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75353502299210845304962193 56515126724408133978721645)
  ·
    refine ⟨21193172521653050242020617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56515126724408133978721645 21193172521653050242020617)
    ·
      refine ⟨15894879391239787681515463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21193172521653050242020617 15894879391239787681515463)
      ·
        refine ⟨23842319086859681522273195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894879391239787681515463 23842319086859681522273195)
        ·
          refine ⟨35763478630289522283409793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23842319086859681522273195 35763478630289522283409793)
          ·
            refine ⟨26822608972717141712557345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35763478630289522283409793 26822608972717141712557345)
            ·
              refine ⟨20116956729537856284418009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26822608972717141712557345 20116956729537856284418009)
              ·
                refine ⟨15087717547153392213313507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20116956729537856284418009 15087717547153392213313507)
                ·
                  refine ⟨22631576320730088319970261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15087717547153392213313507 22631576320730088319970261)
                  ·
                    refine ⟨530427570017111444999303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22631576320730088319970261 530427570017111444999303)
                    ·
                      rfl

theorem cell23_3099012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3099012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099012 prefixEnd_3099012 := by exact prefixLift 3099012
  have htrace : WordTrace (prefixWord ++ tailWord_3099012) baseStart_3099012 baseEnd_3099012 := by
    simpa [prefixWord, tailWord_3099012, baseEnd_3099012] using wordTrace_append hprefix tailTrace_3099012
  have hstable : (prefixWord ++ tailWord_3099012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099012).length < 2 ^ (prefixWord ++ tailWord_3099012).sum := by decide
  have hdescent : baseEnd_3099012 < baseStart_3099012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099069 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_3099069 : Nat := 118140960795 + 3099069 * 2 ^ 59
def prefixEnd_3099069 : Nat := 4983230072969 + 3 ^ 40 * 3099069 * 2
def baseEnd_3099069 : Nat := 1591311978448640611985147

theorem tailTrace_3099069 : CollatzResearch.WordTrace tailWord_3099069 prefixEnd_3099069 1591311978448640611985147 := by
  unfold tailWord_3099069
  simp only [CollatzResearch.WordTrace]
  refine ⟨113032332409609766692268261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75354888273073177794845507 113032332409609766692268261)
  ·
    refine ⟨21193562326801831254800299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113032332409609766692268261 21193562326801831254800299)
    ·
      refine ⟨31790343490202746882200449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21193562326801831254800299 31790343490202746882200449)
      ·
        refine ⟨23842757617652060161650337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31790343490202746882200449 23842757617652060161650337)
        ·
          refine ⟨17882068213239045121237753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23842757617652060161650337 17882068213239045121237753)
          ·
            refine ⟨13411551159929283840928315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17882068213239045121237753 13411551159929283840928315)
            ·
              refine ⟨20117326739893925761392473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411551159929283840928315 20117326739893925761392473)
              ·
                refine ⟨15087995054920444321044355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20117326739893925761392473 15087995054920444321044355)
                ·
                  refine ⟨22631992582380666481566533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15087995054920444321044355 22631992582380666481566533)
                  ·
                    refine ⟨4243498609196374965293725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22631992582380666481566533 4243498609196374965293725)
                    ·
                      refine ⟨1591311978448640611985147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243498609196374965293725 1591311978448640611985147)
                      ·
                        rfl

theorem cell23_3099069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_3099069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099069 prefixEnd_3099069 := by exact prefixLift 3099069
  have htrace : WordTrace (prefixWord ++ tailWord_3099069) baseStart_3099069 baseEnd_3099069 := by
    simpa [prefixWord, tailWord_3099069, baseEnd_3099069] using wordTrace_append hprefix tailTrace_3099069
  have hstable : (prefixWord ++ tailWord_3099069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099069).length < 2 ^ (prefixWord ++ tailWord_3099069).sum := by decide
  have hdescent : baseEnd_3099069 < baseStart_3099069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099093 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_3099093 : Nat := 118140960795 + 3099093 * 2 ^ 59
def prefixEnd_3099093 : Nat := 4983230072969 + 3 ^ 40 * 3099093 * 2
def baseEnd_3099093 : Nat := 530441433994782839361679

theorem tailTrace_3099093 : CollatzResearch.WordTrace tailWord_3099093 prefixEnd_3099093 530441433994782839361679 := by
  unfold tailWord_3099093
  simp only [CollatzResearch.WordTrace]
  refine ⟨113033207761522818791141933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75355471841015212527427955 113033207761522818791141933)
  ·
    refine ⟨42387452910571057046678225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113033207761522818791141933 42387452910571057046678225)
    ·
      refine ⟨31790589682928292785008669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42387452910571057046678225 31790589682928292785008669)
      ·
        refine ⟨11921471131098109794378251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31790589682928292785008669 11921471131098109794378251)
        ·
          refine ⟨17882206696647164691567377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921471131098109794378251 17882206696647164691567377)
          ·
            refine ⟨13411655022485373518675533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17882206696647164691567377 13411655022485373518675533)
            ·
              refine ⟨5029370633432015069503325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13411655022485373518675533 5029370633432015069503325)
              ·
                refine ⟨1886013987537005651063747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5029370633432015069503325 1886013987537005651063747)
                ·
                  refine ⟨2829020981305508476595621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886013987537005651063747 2829020981305508476595621)
                  ·
                    refine ⟨530441433994782839361679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2829020981305508476595621 530441433994782839361679)
                    ·
                      rfl

theorem cell23_3099093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_3099093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099093 prefixEnd_3099093 := by exact prefixLift 3099093
  have htrace : WordTrace (prefixWord ++ tailWord_3099093) baseStart_3099093 baseEnd_3099093 := by
    simpa [prefixWord, tailWord_3099093, baseEnd_3099093] using wordTrace_append hprefix tailTrace_3099093
  have hstable : (prefixWord ++ tailWord_3099093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099093).length < 2 ^ (prefixWord ++ tailWord_3099093).sum := by decide
  have hdescent : baseEnd_3099093 < baseStart_3099093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099139 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 4]
def baseStart_3099139 : Nat := 118140960795 + 3099139 * 2 ^ 59
def prefixEnd_3099139 : Nat := 4983230072969 + 3 ^ 40 * 3099139 * 2
def baseEnd_3099139 : Nat := 1591347922094455338109825

theorem tailTrace_3099139 : CollatzResearch.WordTrace tailWord_3099139 prefixEnd_3099139 1591347922094455338109825 := by
  unfold tailWord_3099139
  simp only [CollatzResearch.WordTrace]
  refine ⟨113034885519356168647316471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75356590346237445764877647 113034885519356168647316471)
  ·
    refine ⟨169552328279034252970974707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113034885519356168647316471 169552328279034252970974707)
    ·
      refine ⟨254328492418551379456462061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169552328279034252970974707 254328492418551379456462061)
      ·
        refine ⟨95373184656956767296173273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254328492418551379456462061 95373184656956767296173273)
        ·
          refine ⟨71529888492717575472129955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95373184656956767296173273 71529888492717575472129955)
          ·
            refine ⟨107294832739076363208194933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71529888492717575472129955 107294832739076363208194933)
            ·
              refine ⟨10058890569288409050768275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107294832739076363208194933 10058890569288409050768275)
              ·
                refine ⟨15088335853932613576152413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10058890569288409050768275 15088335853932613576152413)
                ·
                  refine ⟨5658125945224730091057155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15088335853932613576152413 5658125945224730091057155)
                  ·
                    refine ⟨8487188917837095136585733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5658125945224730091057155 8487188917837095136585733)
                    ·
                      refine ⟨1591347922094455338109825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8487188917837095136585733 1591347922094455338109825)
                      ·
                        rfl

theorem cell23_3099139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_3099139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099139 prefixEnd_3099139 := by exact prefixLift 3099139
  have htrace : WordTrace (prefixWord ++ tailWord_3099139) baseStart_3099139 baseEnd_3099139 := by
    simpa [prefixWord, tailWord_3099139, baseEnd_3099139] using wordTrace_append hprefix tailTrace_3099139
  have hstable : (prefixWord ++ tailWord_3099139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099139).length < 2 ^ (prefixWord ++ tailWord_3099139).sum := by decide
  have hdescent : baseEnd_3099139 < baseStart_3099139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099169 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3099169 : Nat := 118140960795 + 3099169 * 2 ^ 59
def prefixEnd_3099169 : Nat := 4983230072969 + 3 ^ 40 * 3099169 * 2
def baseEnd_3099169 : Nat := 1591363326514090220734687

theorem tailTrace_3099169 : CollatzResearch.WordTrace tailWord_3099169 prefixEnd_3099169 1591363326514090220734687 := by
  unfold tailWord_3099169
  simp only [CollatzResearch.WordTrace]
  refine ⟨113035979709247483770908561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75357319806164989180605707 113035979709247483770908561)
  ·
    refine ⟨84776984781935612828181421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113035979709247483770908561 84776984781935612828181421)
    ·
      refine ⟨31791369293225854810568033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84776984781935612828181421 31791369293225854810568033)
      ·
        refine ⟨23843526969919391107926025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31791369293225854810568033 23843526969919391107926025)
        ·
          refine ⟨17882645227439543330944519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23843526969919391107926025 17882645227439543330944519)
          ·
            refine ⟨26823967841159314996416779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17882645227439543330944519 26823967841159314996416779)
            ·
              refine ⟨40235951761738972494625169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26823967841159314996416779 40235951761738972494625169)
              ·
                refine ⟨30176963821304229370968877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40235951761738972494625169 30176963821304229370968877)
                ·
                  refine ⟨11316361432989086014113329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30176963821304229370968877 11316361432989086014113329)
                  ·
                    refine ⟨8487271074741814510584997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11316361432989086014113329 8487271074741814510584997)
                    ·
                      refine ⟨1591363326514090220734687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8487271074741814510584997 1591363326514090220734687)
                      ·
                        rfl

theorem cell23_3099169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3099169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099169 prefixEnd_3099169 := by exact prefixLift 3099169
  have htrace : WordTrace (prefixWord ++ tailWord_3099169) baseStart_3099169 baseEnd_3099169 := by
    simpa [prefixWord, tailWord_3099169, baseEnd_3099169] using wordTrace_append hprefix tailTrace_3099169
  have hstable : (prefixWord ++ tailWord_3099169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099169).length < 2 ^ (prefixWord ++ tailWord_3099169).sum := by decide
  have hdescent : baseEnd_3099169 < baseStart_3099169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099190 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_3099190 : Nat := 118140960795 + 3099190 * 2 ^ 59
def prefixEnd_3099190 : Nat := 4983230072969 + 3 ^ 40 * 3099190 * 2
def baseEnd_3099190 : Nat := 1591374109607834638572091

theorem tailTrace_3099190 : CollatzResearch.WordTrace tailWord_3099190 prefixEnd_3099190 1591374109607834638572091 := by
  unfold tailWord_3099190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064796602635712772338939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75357830428114269571615349 7064796602635712772338939)
  ·
    refine ⟨10597194903953569158508409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064796602635712772338939 10597194903953569158508409)
    ·
      refine ⟨7947896177965176868881307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10597194903953569158508409 7947896177965176868881307)
      ·
        refine ⟨11921844266947765303321961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7947896177965176868881307 11921844266947765303321961)
        ·
          refine ⟨8941383200210823977491471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11921844266947765303321961 8941383200210823977491471)
          ·
            refine ⟨13412074800316235966237207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8941383200210823977491471 13412074800316235966237207)
            ·
              refine ⟨20118112200474353949355811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13412074800316235966237207 20118112200474353949355811)
              ·
                refine ⟨30177168300711530924033717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20118112200474353949355811 30177168300711530924033717)
                ·
                  refine ⟨2829109528191706024128161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30177168300711530924033717 2829109528191706024128161)
                  ·
                    refine ⟨2121832146143779518096121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829109528191706024128161 2121832146143779518096121)
                    ·
                      refine ⟨1591374109607834638572091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121832146143779518096121 1591374109607834638572091)
                      ·
                        rfl

theorem cell23_3099190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_3099190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099190 prefixEnd_3099190 := by exact prefixLift 3099190
  have htrace : WordTrace (prefixWord ++ tailWord_3099190) baseStart_3099190 baseEnd_3099190 := by
    simpa [prefixWord, tailWord_3099190, baseEnd_3099190] using wordTrace_append hprefix tailTrace_3099190
  have hstable : (prefixWord ++ tailWord_3099190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099190).length < 2 ^ (prefixWord ++ tailWord_3099190).sum := by decide
  have hdescent : baseEnd_3099190 < baseStart_3099190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099196 : List Nat := [2, 2, 2, 2, 3, 2, 3, 7]
def baseStart_3099196 : Nat := 118140960795 + 3099196 * 2 ^ 59
def prefixEnd_3099196 : Nat := 4983230072969 + 3 ^ 40 * 3099196 * 2
def baseEnd_3099196 : Nat := 58939895944139319077669

theorem tailTrace_3099196 : CollatzResearch.WordTrace tailWord_3099196 prefixEnd_3099196 58939895944139319077669 := by
  unfold tailWord_3099196
  simp only [CollatzResearch.WordTrace]
  refine ⟨56518482240074833691070721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75357976320099778254760961 56518482240074833691070721)
  ·
    refine ⟨42388861680056125268303041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56518482240074833691070721 42388861680056125268303041)
    ·
      refine ⟨31791646260042093951227281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42388861680056125268303041 31791646260042093951227281)
      ·
        refine ⟨23843734695031570463420461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31791646260042093951227281 23843734695031570463420461)
        ·
          refine ⟨8941400510636838923782673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23843734695031570463420461 8941400510636838923782673)
          ·
            refine ⟨6706050382977629192837005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8941400510636838923782673 6706050382977629192837005)
            ·
              refine ⟨2514768893616610947313877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6706050382977629192837005 2514768893616610947313877)
              ·
                refine ⟨58939895944139319077669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2514768893616610947313877 58939895944139319077669)
                ·
                  rfl

theorem cell23_3099196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 7].length) (baseStart_3099196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099196 prefixEnd_3099196 := by exact prefixLift 3099196
  have htrace : WordTrace (prefixWord ++ tailWord_3099196) baseStart_3099196 baseEnd_3099196 := by
    simpa [prefixWord, tailWord_3099196, baseEnd_3099196] using wordTrace_append hprefix tailTrace_3099196
  have hstable : (prefixWord ++ tailWord_3099196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099196).length < 2 ^ (prefixWord ++ tailWord_3099196).sum := by decide
  have hdescent : baseEnd_3099196 < baseStart_3099196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099204 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3099204 : Nat := 118140960795 + 3099204 * 2 ^ 59
def prefixEnd_3099204 : Nat := 4983230072969 + 3 ^ 40 * 3099204 * 2
def baseEnd_3099204 : Nat := 530460432778999194599009

theorem tailTrace_3099204 : CollatzResearch.WordTrace tailWord_3099204 prefixEnd_3099204 530460432778999194599009 := by
  unfold tailWord_3099204
  simp only [CollatzResearch.WordTrace]
  refine ⟨56518628132060342374216333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75358170842747123165621777 56518628132060342374216333)
  ·
    refine ⟨21194485549522628390331125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56518628132060342374216333 21194485549522628390331125)
    ·
      refine ⟨1986983020267746411593543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21194485549522628390331125 1986983020267746411593543)
      ·
        refine ⟨2980474530401619617390315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986983020267746411593543 2980474530401619617390315)
        ·
          refine ⟨4470711795602429426085473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980474530401619617390315 4470711795602429426085473)
          ·
            refine ⟨3353033846701822069564105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4470711795602429426085473 3353033846701822069564105)
            ·
              refine ⟨2514775385026366552173079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353033846701822069564105 2514775385026366552173079)
              ·
                refine ⟨3772163077539549828259619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514775385026366552173079 3772163077539549828259619)
                ·
                  refine ⟨5658244616309324742389429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772163077539549828259619 5658244616309324742389429)
                  ·
                    refine ⟨530460432778999194599009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5658244616309324742389429 530460432778999194599009)
                    ·
                      rfl

theorem cell23_3099204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3099204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099204 prefixEnd_3099204 := by exact prefixLift 3099204
  have htrace : WordTrace (prefixWord ++ tailWord_3099204) baseStart_3099204 baseEnd_3099204 := by
    simpa [prefixWord, tailWord_3099204, baseEnd_3099204] using wordTrace_append hprefix tailTrace_3099204
  have hstable : (prefixWord ++ tailWord_3099204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099204).length < 2 ^ (prefixWord ++ tailWord_3099204).sum := by decide
  have hdescent : baseEnd_3099204 < baseStart_3099204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099207 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_3099207 : Nat := 118140960795 + 3099207 * 2 ^ 59
def prefixEnd_3099207 : Nat := 4983230072969 + 3 ^ 40 * 3099207 * 2
def baseEnd_3099207 : Nat := 1591382838778961072059513

theorem tailTrace_3099207 : CollatzResearch.WordTrace tailWord_3099207 prefixEnd_3099207 1591382838778961072059513 := by
  unfold tailWord_3099207
  simp only [CollatzResearch.WordTrace]
  refine ⟨113037365683109816260791875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75358243788739877507194583 113037365683109816260791875)
  ·
    refine ⟨169556048524664724391187813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113037365683109816260791875 169556048524664724391187813)
    ·
      refine ⟨31791759098374635823347715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169556048524664724391187813 31791759098374635823347715)
      ·
        refine ⟨47687638647561953735021573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31791759098374635823347715 47687638647561953735021573)
        ·
          refine ⟨8941432246417866325316545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47687638647561953735021573 8941432246417866325316545)
          ·
            refine ⟨6706074184813399743987409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8941432246417866325316545 6706074184813399743987409)
            ·
              refine ⟨5029555638610049807990557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706074184813399743987409 5029555638610049807990557)
              ·
                refine ⟨1886083364478768677996459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5029555638610049807990557 1886083364478768677996459)
                ·
                  refine ⟨2829125046718153016994689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886083364478768677996459 2829125046718153016994689)
                  ·
                    refine ⟨2121843785038614762746017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829125046718153016994689 2121843785038614762746017)
                    ·
                      refine ⟨1591382838778961072059513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121843785038614762746017 1591382838778961072059513)
                      ·
                        rfl

theorem cell23_3099207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_3099207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099207 prefixEnd_3099207 := by exact prefixLift 3099207
  have htrace : WordTrace (prefixWord ++ tailWord_3099207) baseStart_3099207 baseEnd_3099207 := by
    simpa [prefixWord, tailWord_3099207, baseEnd_3099207] using wordTrace_append hprefix tailTrace_3099207
  have hstable : (prefixWord ++ tailWord_3099207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099207).length < 2 ^ (prefixWord ++ tailWord_3099207).sum := by decide
  have hdescent : baseEnd_3099207 < baseStart_3099207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099210 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_3099210 : Nat := 118140960795 + 3099210 * 2 ^ 59
def prefixEnd_3099210 : Nat := 4983230072969 + 3 ^ 40 * 3099210 * 2
def baseEnd_3099210 : Nat := 1591384379220924560321999

theorem tailTrace_3099210 : CollatzResearch.WordTrace tailWord_3099210 prefixEnd_3099210 1591384379220924560321999 := by
  unfold tailWord_3099210
  simp only [CollatzResearch.WordTrace]
  refine ⟨28259368775524736943287771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75358316734732631848767389 28259368775524736943287771)
  ·
    refine ⟨42389053163287105414931657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28259368775524736943287771 42389053163287105414931657)
    ·
      refine ⟨31791789872465329061198743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42389053163287105414931657 31791789872465329061198743)
      ·
        refine ⟨47687684808697993591798115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31791789872465329061198743 47687684808697993591798115)
        ·
          refine ⟨71531527213046990387697173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47687684808697993591798115 71531527213046990387697173)
          ·
            refine ⟨3353040338111577674423305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71531527213046990387697173 3353040338111577674423305)
            ·
              refine ⟨2514780253583683255817479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353040338111577674423305 2514780253583683255817479)
              ·
                refine ⟨3772170380375524883726219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514780253583683255817479 3772170380375524883726219)
                ·
                  refine ⟨5658255570563287325589329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772170380375524883726219 5658255570563287325589329)
                  ·
                    refine ⟨4243691677922465494191997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5658255570563287325589329 4243691677922465494191997)
                    ·
                      refine ⟨1591384379220924560321999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243691677922465494191997 1591384379220924560321999)
                      ·
                        rfl

theorem cell23_3099210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_3099210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099210 prefixEnd_3099210 := by exact prefixLift 3099210
  have htrace : WordTrace (prefixWord ++ tailWord_3099210) baseStart_3099210 baseEnd_3099210 := by
    simpa [prefixWord, tailWord_3099210, baseEnd_3099210] using wordTrace_append hprefix tailTrace_3099210
  have hstable : (prefixWord ++ tailWord_3099210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099210).length < 2 ^ (prefixWord ++ tailWord_3099210).sum := by decide
  have hdescent : baseEnd_3099210 < baseStart_3099210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099216 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 5, 3, 2]
def baseStart_3099216 : Nat := 118140960795 + 3099216 * 2 ^ 59
def prefixEnd_3099216 : Nat := 4983230072969 + 3 ^ 40 * 3099216 * 2
def baseEnd_3099216 : Nat := 1591387460104851536846971

theorem tailTrace_3099216 : CollatzResearch.WordTrace tailWord_3099216 prefixEnd_3099216 1591387460104851536846971 := by
  unfold tailWord_3099216
  simp only [CollatzResearch.WordTrace]
  refine ⟨56518846970038605398934751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75358462626718140531913001 56518846970038605398934751)
  ·
    refine ⟨84778270455057908098402127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56518846970038605398934751 84778270455057908098402127)
    ·
      refine ⟨127167405682586862147603191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84778270455057908098402127 127167405682586862147603191)
      ·
        refine ⟨190751108523880293221404787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127167405682586862147603191 190751108523880293221404787)
        ·
          refine ⟨286126662785820439832107181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190751108523880293221404787 286126662785820439832107181)
          ·
            refine ⟨107297498544682664937040193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286126662785820439832107181 107297498544682664937040193)
            ·
              refine ⟨80473123908511998702780145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107297498544682664937040193 80473123908511998702780145)
              ·
                refine ⟨60354842931383999027085109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80473123908511998702780145 60354842931383999027085109)
                ·
                  refine ⟨5658266524817249908789229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60354842931383999027085109 5658266524817249908789229)
                  ·
                    refine ⟨2121849946806468715795961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5658266524817249908789229 2121849946806468715795961)
                    ·
                      refine ⟨1591387460104851536846971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121849946806468715795961 1591387460104851536846971)
                      ·
                        rfl

theorem cell23_3099216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 3, 2].length) (baseStart_3099216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099216 prefixEnd_3099216 := by exact prefixLift 3099216
  have htrace : WordTrace (prefixWord ++ tailWord_3099216) baseStart_3099216 baseEnd_3099216 := by
    simpa [prefixWord, tailWord_3099216, baseEnd_3099216] using wordTrace_append hprefix tailTrace_3099216
  have hstable : (prefixWord ++ tailWord_3099216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099216).length < 2 ^ (prefixWord ++ tailWord_3099216).sum := by decide
  have hdescent : baseEnd_3099216 < baseStart_3099216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099240 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3099240 : Nat := 118140960795 + 3099240 * 2 ^ 59
def prefixEnd_3099240 : Nat := 4983230072969 + 3 ^ 40 * 3099240 * 2
def baseEnd_3099240 : Nat := 1591399783640559442946861

theorem tailTrace_3099240 : CollatzResearch.WordTrace tailWord_3099240 prefixEnd_3099240 1591399783640559442946861 := by
  unfold tailWord_3099240
  simp only [CollatzResearch.WordTrace]
  refine ⟨56519284645995131448371587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75359046194660175264495449 56519284645995131448371587)
  ·
    refine ⟨84778926968992697172557381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56519284645995131448371587 84778926968992697172557381)
    ·
      refine ⟨15896048806686130719854509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84778926968992697172557381 15896048806686130719854509)
      ·
        refine ⟨5961018302507299019945441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15896048806686130719854509 5961018302507299019945441)
        ·
          refine ⟨4470763726880474264959081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5961018302507299019945441 4470763726880474264959081)
          ·
            refine ⟨3353072795160355698719311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4470763726880474264959081 3353072795160355698719311)
            ·
              refine ⟨5029609192740533548078967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353072795160355698719311 5029609192740533548078967)
              ·
                refine ⟨7544413789110800322118451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029609192740533548078967 7544413789110800322118451)
                ·
                  refine ⟨11316620683666200483177677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544413789110800322118451 11316620683666200483177677)
                  ·
                    refine ⟨4243732756374825181191629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11316620683666200483177677 4243732756374825181191629)
                    ·
                      refine ⟨1591399783640559442946861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243732756374825181191629 1591399783640559442946861)
                      ·
                        rfl

theorem cell23_3099240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3099240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099240 prefixEnd_3099240 := by exact prefixLift 3099240
  have htrace : WordTrace (prefixWord ++ tailWord_3099240) baseStart_3099240 baseEnd_3099240 := by
    simpa [prefixWord, tailWord_3099240, baseEnd_3099240] using wordTrace_append hprefix tailTrace_3099240
  have hstable : (prefixWord ++ tailWord_3099240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099240).length < 2 ^ (prefixWord ++ tailWord_3099240).sum := by decide
  have hdescent : baseEnd_3099240 < baseStart_3099240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099259 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4]
def baseStart_3099259 : Nat := 118140960795 + 3099259 * 2 ^ 59
def prefixEnd_3099259 : Nat := 4983230072969 + 3 ^ 40 * 3099259 * 2
def baseEnd_3099259 : Nat := 1591409539772994868609273

theorem tailTrace_3099259 : CollatzResearch.WordTrace tailWord_3099259 prefixEnd_3099259 1591409539772994868609273 := by
  unfold tailWord_3099259
  simp only [CollatzResearch.WordTrace]
  refine ⟨113039262278921429141684831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75359508185947619427789887 113039262278921429141684831)
  ·
    refine ⟨169558893418382143712527247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113039262278921429141684831 169558893418382143712527247)
    ·
      refine ⟨254338340127573215568790871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169558893418382143712527247 254338340127573215568790871)
      ·
        refine ⟨381507510191359823353186307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254338340127573215568790871 381507510191359823353186307)
        ·
          refine ⟨572261265287039735029779461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381507510191359823353186307 572261265287039735029779461)
          ·
            refine ⟨107298987241319950318083649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 572261265287039735029779461 107298987241319950318083649)
            ·
              refine ⟨80474240430989962738562737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107298987241319950318083649 80474240430989962738562737)
              ·
                refine ⟨60355680323242472053922053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80474240430989962738562737 60355680323242472053922053)
                ·
                  refine ⟨11316690060607963510110385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60355680323242472053922053 11316690060607963510110385)
                  ·
                    refine ⟨8487517545455972632582789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11316690060607963510110385 8487517545455972632582789)
                    ·
                      refine ⟨1591409539772994868609273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8487517545455972632582789 1591409539772994868609273)
                      ·
                        rfl

theorem cell23_3099259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_3099259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099259 prefixEnd_3099259 := by exact prefixLift 3099259
  have htrace : WordTrace (prefixWord ++ tailWord_3099259) baseStart_3099259 baseEnd_3099259 := by
    simpa [prefixWord, tailWord_3099259, baseEnd_3099259] using wordTrace_append hprefix tailTrace_3099259
  have hstable : (prefixWord ++ tailWord_3099259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099259).length < 2 ^ (prefixWord ++ tailWord_3099259).sum := by decide
  have hdescent : baseEnd_3099259 < baseStart_3099259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099297 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3099297 : Nat := 118140960795 + 3099297 * 2 ^ 59
def prefixEnd_3099297 : Nat := 4983230072969 + 3 ^ 40 * 3099297 * 2
def baseEnd_3099297 : Nat := 1591429052037865719934099

theorem tailTrace_3099297 : CollatzResearch.WordTrace tailWord_3099297 prefixEnd_3099297 1591429052037865719934099 := by
  unfold tailWord_3099297
  simp only [CollatzResearch.WordTrace]
  refine ⟨113040648252783761631568145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75360432168522507754378763 113040648252783761631568145)
  ·
    refine ⟨84780486189587821223676109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113040648252783761631568145 84780486189587821223676109)
    ·
      refine ⟨31792682321095432958878541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84780486189587821223676109 31792682321095432958878541)
      ·
        refine ⟨11922255870410787359579453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31792682321095432958878541 11922255870410787359579453)
        ·
          refine ⟨4470845951404045259842295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11922255870410787359579453 4470845951404045259842295)
          ·
            refine ⟨6706268927106067889763443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470845951404045259842295 6706268927106067889763443)
            ·
              refine ⟨10059403390659101834645165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706268927106067889763443 10059403390659101834645165)
              ·
                refine ⟨3772276271497163187991937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10059403390659101834645165 3772276271497163187991937)
                ·
                  refine ⟨2829207203622872390993953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3772276271497163187991937 2829207203622872390993953)
                  ·
                    refine ⟨2121905402717154293245465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829207203622872390993953 2121905402717154293245465)
                    ·
                      refine ⟨1591429052037865719934099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121905402717154293245465 1591429052037865719934099)
                      ·
                        rfl

theorem cell23_3099297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3099297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099297 prefixEnd_3099297 := by exact prefixLift 3099297
  have htrace : WordTrace (prefixWord ++ tailWord_3099297) baseStart_3099297 baseEnd_3099297 := by
    simpa [prefixWord, tailWord_3099297, baseEnd_3099297] using wordTrace_append hprefix tailTrace_3099297
  have hstable : (prefixWord ++ tailWord_3099297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099297).length < 2 ^ (prefixWord ++ tailWord_3099297).sum := by decide
  have hdescent : baseEnd_3099297 < baseStart_3099297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099299 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 1, 7]
def baseStart_3099299 : Nat := 118140960795 + 3099299 * 2 ^ 59
def prefixEnd_3099299 : Nat := 4983230072969 + 3 ^ 40 * 3099299 * 2
def baseEnd_3099299 : Nat := 530476692999724904036363

theorem tailTrace_3099299 : CollatzResearch.WordTrace tailWord_3099299 prefixEnd_3099299 530476692999724904036363 := by
  unfold tailWord_3099299
  simp only [CollatzResearch.WordTrace]
  refine ⟨113040721198776515973140951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75360480799184343982093967 113040721198776515973140951)
  ·
    refine ⟨169561081798164773959711427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113040721198776515973140951 169561081798164773959711427)
    ·
      refine ⟨254341622697247160939567141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169561081798164773959711427 254341622697247160939567141)
      ·
        refine ⟨47689054255733842676168839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254341622697247160939567141 47689054255733842676168839)
        ·
          refine ⟨71533581383600764014253259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47689054255733842676168839 71533581383600764014253259)
          ·
            refine ⟨107300372075401146021379889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71533581383600764014253259 107300372075401146021379889)
            ·
              refine ⟨80475279056550859516034917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107300372075401146021379889 80475279056550859516034917)
              ·
                refine ⟨15089114823103286159256547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80475279056550859516034917 15089114823103286159256547)
                ·
                  refine ⟨22633672234654929238884821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15089114823103286159256547 22633672234654929238884821)
                  ·
                    refine ⟨530476692999724904036363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22633672234654929238884821 530476692999724904036363)
                    ·
                      rfl

theorem cell23_3099299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 7].length) (baseStart_3099299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099299 prefixEnd_3099299 := by exact prefixLift 3099299
  have htrace : WordTrace (prefixWord ++ tailWord_3099299) baseStart_3099299 baseEnd_3099299 := by
    simpa [prefixWord, tailWord_3099299, baseEnd_3099299] using wordTrace_append hprefix tailTrace_3099299
  have hstable : (prefixWord ++ tailWord_3099299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099299).length < 2 ^ (prefixWord ++ tailWord_3099299).sum := by decide
  have hdescent : baseEnd_3099299 < baseStart_3099299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099326 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3099326 : Nat := 118140960795 + 3099326 * 2 ^ 59
def prefixEnd_3099326 : Nat := 4983230072969 + 3 ^ 40 * 3099326 * 2
def baseEnd_3099326 : Nat := 1591443942976846106471465

theorem tailTrace_3099326 : CollatzResearch.WordTrace tailWord_3099326 prefixEnd_3099326 1591443942976846106471465 := by
  unfold tailWord_3099326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130213246209837448046729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75361137313119133056249221 14130213246209837448046729)
  ·
    refine ⟨10597659934657378086035047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14130213246209837448046729 10597659934657378086035047)
    ·
      refine ⟨15896489901986067129052571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10597659934657378086035047 15896489901986067129052571)
      ·
        refine ⟨23844734852979100693578857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15896489901986067129052571 23844734852979100693578857)
        ·
          refine ⟨17883551139734325520184143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23844734852979100693578857 17883551139734325520184143)
          ·
            refine ⟨26825326709601488280276215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17883551139734325520184143 26825326709601488280276215)
            ·
              refine ⟨40237990064402232420414323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26825326709601488280276215 40237990064402232420414323)
              ·
                refine ⟨60356985096603348630621485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40237990064402232420414323 60356985096603348630621485)
                ·
                  refine ⟨22633869411226255736483057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60356985096603348630621485 22633869411226255736483057)
                  ·
                    refine ⟨16975402058419691802362293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22633869411226255736483057 16975402058419691802362293)
                    ·
                      refine ⟨1591443942976846106471465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16975402058419691802362293 1591443942976846106471465)
                      ·
                        rfl

theorem cell23_3099326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3099326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099326 prefixEnd_3099326 := by exact prefixLift 3099326
  have htrace : WordTrace (prefixWord ++ tailWord_3099326) baseStart_3099326 baseEnd_3099326 := by
    simpa [prefixWord, tailWord_3099326, baseEnd_3099326] using wordTrace_append hprefix tailTrace_3099326
  have hstable : (prefixWord ++ tailWord_3099326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099326).length < 2 ^ (prefixWord ++ tailWord_3099326).sum := by decide
  have hdescent : baseEnd_3099326 < baseStart_3099326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099353 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 2, 4, 2]
def baseStart_3099353 : Nat := 118140960795 + 3099353 * 2 ^ 59
def prefixEnd_3099353 : Nat := 4983230072969 + 3 ^ 40 * 3099353 * 2
def baseEnd_3099353 : Nat := 1591457806954517500833841

theorem tailTrace_3099353 : CollatzResearch.WordTrace tailWord_3099353 prefixEnd_3099353 1591457806954517500833841 := by
  unfold tailWord_3099353
  simp only [CollatzResearch.WordTrace]
  refine ⟨113042690740580883195606713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75361793827053922130404475 113042690740580883195606713)
  ·
    refine ⟨84782018055435662396705035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113042690740580883195606713 84782018055435662396705035)
    ·
      refine ⟨127173027083153493595057553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84782018055435662396705035 127173027083153493595057553)
      ·
        refine ⟨95379770312365120196293165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127173027083153493595057553 95379770312365120196293165)
        ·
          refine ⟨35767413867136920073609937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95379770312365120196293165 35767413867136920073609937)
          ·
            refine ⟨26825560400352690055207453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35767413867136920073609937 26825560400352690055207453)
            ·
              refine ⟨10059585150132258770702795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26825560400352690055207453 10059585150132258770702795)
              ·
                refine ⟨15089377725198388156054193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10059585150132258770702795 15089377725198388156054193)
                ·
                  refine ⟨11317033293898791117040645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15089377725198388156054193 11317033293898791117040645)
                  ·
                    refine ⟨2121943742606023334445121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11317033293898791117040645 2121943742606023334445121)
                    ·
                      refine ⟨1591457806954517500833841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121943742606023334445121 1591457806954517500833841)
                      ·
                        rfl

theorem cell23_3099353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_3099353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099353 prefixEnd_3099353 := by exact prefixLift 3099353
  have htrace : WordTrace (prefixWord ++ tailWord_3099353) baseStart_3099353 baseEnd_3099353 := by
    simpa [prefixWord, tailWord_3099353, baseEnd_3099353] using wordTrace_append hprefix tailTrace_3099353
  have hstable : (prefixWord ++ tailWord_3099353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099353).length < 2 ^ (prefixWord ++ tailWord_3099353).sum := by decide
  have hdescent : baseEnd_3099353 < baseStart_3099353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099363 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 5, 4]
def baseStart_3099363 : Nat := 118140960795 + 3099363 * 2 ^ 59
def prefixEnd_3099363 : Nat := 4983230072969 + 3 ^ 40 * 3099363 * 2
def baseEnd_3099363 : Nat := 530487647253687487236265

theorem tailTrace_3099363 : CollatzResearch.WordTrace tailWord_3099363 prefixEnd_3099363 530487647253687487236265 := by
  unfold tailWord_3099363
  simp only [CollatzResearch.WordTrace]
  refine ⟨113043055470544654903470743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75362036980363103268980495 113043055470544654903470743)
  ·
    refine ⟨169564583205816982355206115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113043055470544654903470743 169564583205816982355206115)
    ·
      refine ⟨254346874808725473532809173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169564583205816982355206115 254346874808725473532809173)
      ·
        refine ⟨5961254878329503285925215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 254346874808725473532809173 5961254878329503285925215)
        ·
          refine ⟨8941882317494254928887823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5961254878329503285925215 8941882317494254928887823)
          ·
            refine ⟨13412823476241382393331735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8941882317494254928887823 13412823476241382393331735)
            ·
              refine ⟨20119235214362073589997603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13412823476241382393331735 20119235214362073589997603)
              ·
                refine ⟨30178852821543110384996405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20119235214362073589997603 30178852821543110384996405)
                ·
                  refine ⟨2829267452019666598593413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30178852821543110384996405 2829267452019666598593413)
                  ·
                    refine ⟨530487647253687487236265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2829267452019666598593413 530487647253687487236265)
                    ·
                      rfl

theorem cell23_3099363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 4].length) (baseStart_3099363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099363 prefixEnd_3099363 := by exact prefixLift 3099363
  have htrace : WordTrace (prefixWord ++ tailWord_3099363) baseStart_3099363 baseEnd_3099363 := by
    simpa [prefixWord, tailWord_3099363, baseEnd_3099363] using wordTrace_append hprefix tailTrace_3099363
  have hstable : (prefixWord ++ tailWord_3099363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099363).length < 2 ^ (prefixWord ++ tailWord_3099363).sum := by decide
  have hdescent : baseEnd_3099363 < baseStart_3099363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099373 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3099373 : Nat := 118140960795 + 3099373 * 2 ^ 59
def prefixEnd_3099373 : Nat := 4983230072969 + 3 ^ 40 * 3099373 * 2
def baseEnd_3099373 : Nat := 1591468076567607422583749

theorem tailTrace_3099373 : CollatzResearch.WordTrace tailWord_3099373 prefixEnd_3099373 1591468076567607422583749 := by
  unfold tailWord_3099373
  simp only [CollatzResearch.WordTrace]
  refine ⟨113043420200508426611334773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75362280133672284407556515 113043420200508426611334773)
  ·
    refine ⟨10597820643797664994812635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113043420200508426611334773 10597820643797664994812635)
    ·
      refine ⟨15896730965696497492218953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10597820643797664994812635 15896730965696497492218953)
      ·
        refine ⟨11922548224272373119164215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15896730965696497492218953 11922548224272373119164215)
        ·
          refine ⟨17883822336408559678746323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11922548224272373119164215 17883822336408559678746323)
          ·
            refine ⟨26825733504612839518119485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17883822336408559678746323 26825733504612839518119485)
            ·
              refine ⟨10059650064229814819294807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26825733504612839518119485 10059650064229814819294807)
              ·
                refine ⟨15089475096344722228942211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10059650064229814819294807 15089475096344722228942211)
                ·
                  refine ⟨22634212644517083343413317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15089475096344722228942211 22634212644517083343413317)
                  ·
                    refine ⟨4243914870846953126889997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22634212644517083343413317 4243914870846953126889997)
                    ·
                      refine ⟨1591468076567607422583749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243914870846953126889997 1591468076567607422583749)
                      ·
                        rfl

theorem cell23_3099373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3099373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099373 prefixEnd_3099373 := by exact prefixLift 3099373
  have htrace : WordTrace (prefixWord ++ tailWord_3099373) baseStart_3099373 baseEnd_3099373 := by
    simpa [prefixWord, tailWord_3099373, baseEnd_3099373] using wordTrace_append hprefix tailTrace_3099373
  have hstable : (prefixWord ++ tailWord_3099373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099373).length < 2 ^ (prefixWord ++ tailWord_3099373).sum := by decide
  have hdescent : baseEnd_3099373 < baseStart_3099373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099396 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3099396 : Nat := 118140960795 + 3099396 * 2 ^ 59
def prefixEnd_3099396 : Nat := 4983230072969 + 3 ^ 40 * 3099396 * 2
def baseEnd_3099396 : Nat := 1591479886622660832596143

theorem tailTrace_3099396 : CollatzResearch.WordTrace tailWord_3099396 prefixEnd_3099396 1591479886622660832596143 := by
  unfold tailWord_3099396
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522129539712550769711021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75362839386283401026281361 56522129539712550769711021)
  ·
    refine ⟨21195798577392206538641633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56522129539712550769711021 21195798577392206538641633)
    ·
      refine ⟨15896848933044154903981225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21195798577392206538641633 15896848933044154903981225)
      ·
        refine ⟨11922636699783116177985919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15896848933044154903981225 11922636699783116177985919)
        ·
          refine ⟨17883955049674674266978879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11922636699783116177985919 17883955049674674266978879)
          ·
            refine ⟨26825932574512011400468319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17883955049674674266978879 26825932574512011400468319)
            ·
              refine ⟨40238898861768017100702479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26825932574512011400468319 40238898861768017100702479)
              ·
                refine ⟨60358348292652025651053719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40238898861768017100702479 60358348292652025651053719)
                ·
                  refine ⟨90537522438978038476580579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60358348292652025651053719 90537522438978038476580579)
                  ·
                    refine ⟨135806283658467057714870869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90537522438978038476580579 135806283658467057714870869)
                    ·
                      refine ⟨1591479886622660832596143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 135806283658467057714870869 1591479886622660832596143)
                      ·
                        rfl

theorem cell23_3099396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3099396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099396 prefixEnd_3099396 := by exact prefixLift 3099396
  have htrace : WordTrace (prefixWord ++ tailWord_3099396) baseStart_3099396 baseEnd_3099396 := by
    simpa [prefixWord, tailWord_3099396, baseEnd_3099396] using wordTrace_append hprefix tailTrace_3099396
  have hstable : (prefixWord ++ tailWord_3099396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099396).length < 2 ^ (prefixWord ++ tailWord_3099396).sum := by decide
  have hdescent : baseEnd_3099396 < baseStart_3099396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099413 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_3099413 : Nat := 118140960795 + 3099413 * 2 ^ 59
def prefixEnd_3099413 : Nat := 4983230072969 + 3 ^ 40 * 3099413 * 2
def baseEnd_3099413 : Nat := 1591488615793787266083565

theorem tailTrace_3099413 : CollatzResearch.WordTrace tailWord_3099413 prefixEnd_3099413 1591488615793787266083565 := by
  unfold tailWord_3099413
  simp only [CollatzResearch.WordTrace]
  refine ⟨113044879120363513442790893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75363252746909008961860595 113044879120363513442790893)
  ·
    refine ⟨42391829670136317541046585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113044879120363513442790893 42391829670136317541046585)
    ·
      refine ⟨31793872252602238155784939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42391829670136317541046585 31793872252602238155784939)
      ·
        refine ⟨47690808378903357233677409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31793872252602238155784939 47690808378903357233677409)
        ·
          refine ⟨35768106284177517925258057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47690808378903357233677409 35768106284177517925258057)
          ·
            refine ⟨26826079713133138443943543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35768106284177517925258057 26826079713133138443943543)
            ·
              refine ⟨40239119569699707665915315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26826079713133138443943543 40239119569699707665915315)
              ·
                refine ⟨60358679354549561498872973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40239119569699707665915315 60358679354549561498872973)
                ·
                  refine ⟨22634504757956085562077365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60358679354549561498872973 22634504757956085562077365)
                  ·
                    refine ⟨2121984821058383021444753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22634504757956085562077365 2121984821058383021444753)
                    ·
                      refine ⟨1591488615793787266083565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2121984821058383021444753 1591488615793787266083565)
                      ·
                        rfl

theorem cell23_3099413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_3099413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099413 prefixEnd_3099413 := by exact prefixLift 3099413
  have htrace : WordTrace (prefixWord ++ tailWord_3099413) baseStart_3099413 baseEnd_3099413 := by
    simpa [prefixWord, tailWord_3099413, baseEnd_3099413] using wordTrace_append hprefix tailTrace_3099413
  have hstable : (prefixWord ++ tailWord_3099413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099413).length < 2 ^ (prefixWord ++ tailWord_3099413).sum := by decide
  have hdescent : baseEnd_3099413 < baseStart_3099413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099420 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3099420 : Nat := 118140960795 + 3099420 * 2 ^ 59
def prefixEnd_3099420 : Nat := 4983230072969 + 3 ^ 40 * 3099420 * 2
def baseEnd_3099420 : Nat := 1591492210158368738696033

theorem tailTrace_3099420 : CollatzResearch.WordTrace tailWord_3099420 prefixEnd_3099420 1591492210158368738696033 := by
  unfold tailWord_3099420
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522567215669076819147857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75363422954225435758863809 56522567215669076819147857)
  ·
    refine ⟨42391925411751807614360893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56522567215669076819147857 42391925411751807614360893)
    ·
      refine ⟨15896972029406927855385335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42391925411751807614360893 15896972029406927855385335)
      ·
        refine ⟨23845458044110391783078003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15896972029406927855385335 23845458044110391783078003)
        ·
          refine ⟨35768187066165587674617005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23845458044110391783078003 35768187066165587674617005)
          ·
            refine ⟨13413070149812095377981377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35768187066165587674617005 13413070149812095377981377)
            ·
              refine ⟨10059802612359071533486033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13413070149812095377981377 10059802612359071533486033)
              ·
                refine ⟨7544851959269303650114525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10059802612359071533486033 7544851959269303650114525)
                ·
                  refine ⟨2829319484725988868792947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7544851959269303650114525 2829319484725988868792947)
                  ·
                    refine ⟨4243979227088983303189421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2829319484725988868792947 4243979227088983303189421)
                    ·
                      refine ⟨1591492210158368738696033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4243979227088983303189421 1591492210158368738696033)
                      ·
                        rfl

theorem cell23_3099420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3099420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099420 prefixEnd_3099420 := by exact prefixLift 3099420
  have htrace : WordTrace (prefixWord ++ tailWord_3099420) baseStart_3099420 baseEnd_3099420 := by
    simpa [prefixWord, tailWord_3099420, baseEnd_3099420] using wordTrace_append hprefix tailTrace_3099420
  have hstable : (prefixWord ++ tailWord_3099420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099420).length < 2 ^ (prefixWord ++ tailWord_3099420).sum := by decide
  have hdescent : baseEnd_3099420 < baseStart_3099420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099423 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 1, 5]
def baseStart_3099423 : Nat := 118140960795 + 3099423 * 2 ^ 59
def prefixEnd_3099423 : Nat := 4983230072969 + 3 ^ 40 * 3099423 * 2
def baseEnd_3099423 : Nat := 530497916866777408986173

theorem tailTrace_3099423 : CollatzResearch.WordTrace tailWord_3099423 prefixEnd_3099423 530497916866777408986173 := by
  unfold tailWord_3099423
  simp only [CollatzResearch.WordTrace]
  refine ⟨113045243850327285150654923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75363495900218190100436615 113045243850327285150654923)
  ·
    refine ⟨169567865775490927725982385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113045243850327285150654923 169567865775490927725982385)
    ·
      refine ⟨127175899331618195794486789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169567865775490927725982385 127175899331618195794486789)
      ·
        refine ⟨23845481124678411711466273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127175899331618195794486789 23845481124678411711466273)
        ·
          refine ⟨17884110843508808783599705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23845481124678411711466273 17884110843508808783599705)
          ·
            refine ⟨13413083132631606587699779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17884110843508808783599705 13413083132631606587699779)
            ·
              refine ⟨20119624698947409881549669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13413083132631606587699779 20119624698947409881549669)
              ·
                refine ⟨3772429631052639352790563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20119624698947409881549669 3772429631052639352790563)
                ·
                  refine ⟨5658644446578959029185845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772429631052639352790563 5658644446578959029185845)
                  ·
                    refine ⟨530497916866777408986173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5658644446578959029185845 530497916866777408986173)
                    ·
                      rfl

theorem cell23_3099423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_3099423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099423 prefixEnd_3099423 := by exact prefixLift 3099423
  have htrace : WordTrace (prefixWord ++ tailWord_3099423) baseStart_3099423 baseEnd_3099423 := by
    simpa [prefixWord, tailWord_3099423, baseEnd_3099423] using wordTrace_append hprefix tailTrace_3099423
  have hstable : (prefixWord ++ tailWord_3099423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099423).length < 2 ^ (prefixWord ++ tailWord_3099423).sum := by decide
  have hdescent : baseEnd_3099423 < baseStart_3099423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099436 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_3099436 : Nat := 118140960795 + 3099436 * 2 ^ 59
def prefixEnd_3099436 : Nat := 4983230072969 + 3 ^ 40 * 3099436 * 2
def baseEnd_3099436 : Nat := 530500141949613558698653

theorem tailTrace_3099436 : CollatzResearch.WordTrace tailWord_3099436 prefixEnd_3099436 530500141949613558698653 := by
  unfold tailWord_3099436
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522858999640094185439081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75363811999520125580585441 56522858999640094185439081)
  ·
    refine ⟨42392144249730070639079311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56522858999640094185439081 42392144249730070639079311)
    ·
      refine ⟨63588216374595105958618967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42392144249730070639079311 63588216374595105958618967)
      ·
        refine ⟨95382324561892658937928451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63588216374595105958618967 95382324561892658937928451)
        ·
          refine ⟨143073486842838988406892677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95382324561892658937928451 143073486842838988406892677)
          ·
            refine ⟨26826278783032310326292377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143073486842838988406892677 26826278783032310326292377)
            ·
              refine ⟨20119709087274232744719283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26826278783032310326292377 20119709087274232744719283)
              ·
                refine ⟨30179563630911349117078925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20119709087274232744719283 30179563630911349117078925)
                ·
                  refine ⟨11317336361591755918904597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30179563630911349117078925 11317336361591755918904597)
                  ·
                    refine ⟨530500141949613558698653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11317336361591755918904597 530500141949613558698653)
                    ·
                      rfl

theorem cell23_3099436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_3099436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099436 prefixEnd_3099436 := by exact prefixLift 3099436
  have htrace : WordTrace (prefixWord ++ tailWord_3099436) baseStart_3099436 baseEnd_3099436 := by
    simpa [prefixWord, tailWord_3099436, baseEnd_3099436] using wordTrace_append hprefix tailTrace_3099436
  have hstable : (prefixWord ++ tailWord_3099436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099436).length < 2 ^ (prefixWord ++ tailWord_3099436).sum := by decide
  have hdescent : baseEnd_3099436 < baseStart_3099436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099454 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3099454 : Nat := 118140960795 + 3099454 * 2 ^ 59
def prefixEnd_3099454 : Nat := 4983230072969 + 3 ^ 40 * 3099454 * 2
def baseEnd_3099454 : Nat := 1591509668500621605670877

theorem tailTrace_3099454 : CollatzResearch.WordTrace tailWord_3099454 prefixEnd_3099454 1591509668500621605670877 := by
  unfold tailWord_3099454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130796814151872180629177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75364249675476651630022277 14130796814151872180629177)
  ·
    refine ⟨10598097610613904135471883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14130796814151872180629177 10598097610613904135471883)
    ·
      refine ⟨15897146415920856203207825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598097610613904135471883 15897146415920856203207825)
      ·
        refine ⟨11922859811940642152405869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15897146415920856203207825 11922859811940642152405869)
        ·
          refine ⟨4471072429477740807152201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11922859811940642152405869 4471072429477740807152201)
          ·
            refine ⟨3353304322108305605364151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4471072429477740807152201 3353304322108305605364151)
            ·
              refine ⟨5029956483162458408046227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353304322108305605364151 5029956483162458408046227)
              ·
                refine ⟨7544934724743687612069341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029956483162458408046227 7544934724743687612069341)
                ·
                  refine ⟨2829350521778882854526003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7544934724743687612069341 2829350521778882854526003)
                  ·
                    refine ⟨4244025782668324281789005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2829350521778882854526003 4244025782668324281789005)
                    ·
                      refine ⟨1591509668500621605670877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244025782668324281789005 1591509668500621605670877)
                      ·
                        rfl

theorem cell23_3099454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3099454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099454 prefixEnd_3099454 := by exact prefixLift 3099454
  have htrace : WordTrace (prefixWord ++ tailWord_3099454) baseStart_3099454 baseEnd_3099454 := by
    simpa [prefixWord, tailWord_3099454, baseEnd_3099454] using wordTrace_append hprefix tailTrace_3099454
  have hstable : (prefixWord ++ tailWord_3099454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099454).length < 2 ^ (prefixWord ++ tailWord_3099454).sum := by decide
  have hdescent : baseEnd_3099454 < baseStart_3099454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099463 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_3099463 : Nat := 118140960795 + 3099463 * 2 ^ 59
def prefixEnd_3099463 : Nat := 4983230072969 + 3 ^ 40 * 3099463 * 2
def baseEnd_3099463 : Nat := 1591514289826512070458335

theorem tailTrace_3099463 : CollatzResearch.WordTrace tailWord_3099463 prefixEnd_3099463 1591514289826512070458335 := by
  unfold tailWord_3099463
  simp only [CollatzResearch.WordTrace]
  refine ⟨113046702770182371982111043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75364468513454914654740695 113046702770182371982111043)
  ·
    refine ⟨169570054155273557973166565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113046702770182371982111043 169570054155273557973166565)
    ·
      refine ⟨31794385154113792119968731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169570054155273557973166565 31794385154113792119968731)
      ·
        refine ⟨47691577731170688179953097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31794385154113792119968731 47691577731170688179953097)
        ·
          refine ⟨35768683298378016134964823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47691577731170688179953097 35768683298378016134964823)
          ·
            refine ⟨53653024947567024202447235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35768683298378016134964823 53653024947567024202447235)
            ·
              refine ⟨80479537421350536303670853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53653024947567024202447235 80479537421350536303670853)
              ·
                refine ⟨15089913266503225556938285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80479537421350536303670853 15089913266503225556938285)
                ·
                  refine ⟨5658717474938709583851857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15089913266503225556938285 5658717474938709583851857)
                  ·
                    refine ⟨4244038106204032187888893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5658717474938709583851857 4244038106204032187888893)
                    ·
                      refine ⟨1591514289826512070458335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244038106204032187888893 1591514289826512070458335)
                      ·
                        rfl

theorem cell23_3099463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_3099463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099463 prefixEnd_3099463 := by exact prefixLift 3099463
  have htrace : WordTrace (prefixWord ++ tailWord_3099463) baseStart_3099463 baseEnd_3099463 := by
    simpa [prefixWord, tailWord_3099463, baseEnd_3099463] using wordTrace_append hprefix tailTrace_3099463
  have hstable : (prefixWord ++ tailWord_3099463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099463).length < 2 ^ (prefixWord ++ tailWord_3099463).sum := by decide
  have hdescent : baseEnd_3099463 < baseStart_3099463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099493 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3099493 : Nat := 118140960795 + 3099493 * 2 ^ 59
def prefixEnd_3099493 : Nat := 4983230072969 + 3 ^ 40 * 3099493 * 2
def baseEnd_3099493 : Nat := 1591529694246146953083197

theorem tailTrace_3099493 : CollatzResearch.WordTrace tailWord_3099493 prefixEnd_3099493 1591529694246146953083197 := by
  unfold tailWord_3099493
  simp only [CollatzResearch.WordTrace]
  refine ⟨113047796960073687105703133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75365197973382458070468755 113047796960073687105703133)
  ·
    refine ⟨42392923860027632664638675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113047796960073687105703133 42392923860027632664638675)
    ·
      refine ⟨63589385790041448996958013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42392923860027632664638675 63589385790041448996958013)
      ·
        refine ⟨23846019671265543373859255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63589385790041448996958013 23846019671265543373859255)
        ·
          refine ⟨35769029506898315060788883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23846019671265543373859255 35769029506898315060788883)
          ·
            refine ⟨53653544260347472591183325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35769029506898315060788883 53653544260347472591183325)
            ·
              refine ⟨20120079097630302221693747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53653544260347472591183325 20120079097630302221693747)
              ·
                refine ⟨30180118646445453332540621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20120079097630302221693747 30180118646445453332540621)
                ·
                  refine ⟨11317544492417044999702733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30180118646445453332540621 11317544492417044999702733)
                  ·
                    refine ⟨4244079184656391874888525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11317544492417044999702733 4244079184656391874888525)
                    ·
                      refine ⟨1591529694246146953083197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244079184656391874888525 1591529694246146953083197)
                      ·
                        rfl

theorem cell23_3099493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3099493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099493 prefixEnd_3099493 := by exact prefixLift 3099493
  have htrace : WordTrace (prefixWord ++ tailWord_3099493) baseStart_3099493 baseEnd_3099493 := by
    simpa [prefixWord, tailWord_3099493, baseEnd_3099493] using wordTrace_append hprefix tailTrace_3099493
  have hstable : (prefixWord ++ tailWord_3099493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099493).length < 2 ^ (prefixWord ++ tailWord_3099493).sum := by decide
  have hdescent : baseEnd_3099493 < baseStart_3099493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099527 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_3099527 : Nat := 118140960795 + 3099527 * 2 ^ 59
def prefixEnd_3099527 : Nat := 4983230072969 + 3 ^ 40 * 3099527 * 2
def baseEnd_3099527 : Nat := 1591547152588399820058041

theorem tailTrace_3099527 : CollatzResearch.WordTrace tailWord_3099527 prefixEnd_3099527 1591547152588399820058041 := by
  unfold tailWord_3099527
  simp only [CollatzResearch.WordTrace]
  refine ⟨113049037041950510912440835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75366024694633673941627223 113049037041950510912440835)
  ·
    refine ⟨169573555562925766368661253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113049037041950510912440835 169573555562925766368661253)
    ·
      refine ⟨31795041668048581194123985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169573555562925766368661253 31795041668048581194123985)
      ·
        refine ⟨23846281251036435895592989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31795041668048581194123985 23846281251036435895592989)
        ·
          refine ⟨8942355469138663460847371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23846281251036435895592989 8942355469138663460847371)
          ·
            refine ⟨13413533203707995191271057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8942355469138663460847371 13413533203707995191271057)
            ·
              refine ⟨10060149902780996393453293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13413533203707995191271057 10060149902780996393453293)
              ·
                refine ⟨3772556213542873647544985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10060149902780996393453293 3772556213542873647544985)
                ·
                  refine ⟨2829417160157155235658739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3772556213542873647544985 2829417160157155235658739)
                  ·
                    refine ⟨4244125740235732853488109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2829417160157155235658739 4244125740235732853488109)
                    ·
                      refine ⟨1591547152588399820058041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244125740235732853488109 1591547152588399820058041)
                      ·
                        rfl

theorem cell23_3099527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_3099527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099527 prefixEnd_3099527 := by exact prefixLift 3099527
  have htrace : WordTrace (prefixWord ++ tailWord_3099527) baseStart_3099527 baseEnd_3099527 := by
    simpa [prefixWord, tailWord_3099527, baseEnd_3099527] using wordTrace_append hprefix tailTrace_3099527
  have hstable : (prefixWord ++ tailWord_3099527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099527).length < 2 ^ (prefixWord ++ tailWord_3099527).sum := by decide
  have hdescent : baseEnd_3099527 < baseStart_3099527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099554 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_3099554 : Nat := 118140960795 + 3099554 * 2 ^ 59
def prefixEnd_3099554 : Nat := 4983230072969 + 3 ^ 40 * 3099554 * 2
def baseEnd_3099554 : Nat := 1591561016566071214420417

theorem tailTrace_3099554 : CollatzResearch.WordTrace tailWord_3099554 prefixEnd_3099554 1591561016566071214420417 := by
  unfold tailWord_3099554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28262505453213173630918429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75366681208568463015782477 28262505453213173630918429)
  ·
    refine ⟨10598439544954940111594411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28262505453213173630918429 10598439544954940111594411)
    ·
      refine ⟨15897659317432410167391617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598439544954940111594411 15897659317432410167391617)
      ·
        refine ⟨11923244488074307625543713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15897659317432410167391617 11923244488074307625543713)
        ·
          refine ⟨8942433366055730719157785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11923244488074307625543713 8942433366055730719157785)
          ·
            refine ⟨6706825024541798039368339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8942433366055730719157785 6706825024541798039368339)
            ·
              refine ⟨10060237536812697059052509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706825024541798039368339 10060237536812697059052509)
              ·
                refine ⟨3772589076304761397144691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10060237536812697059052509 3772589076304761397144691)
                ·
                  refine ⟨5658883614457142095717037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772589076304761397144691 5658883614457142095717037)
                  ·
                    refine ⟨2122081355421428285893889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5658883614457142095717037 2122081355421428285893889)
                    ·
                      refine ⟨1591561016566071214420417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122081355421428285893889 1591561016566071214420417)
                      ·
                        rfl

theorem cell23_3099554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_3099554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099554 prefixEnd_3099554 := by exact prefixLift 3099554
  have htrace : WordTrace (prefixWord ++ tailWord_3099554) baseStart_3099554 baseEnd_3099554 := by
    simpa [prefixWord, tailWord_3099554, baseEnd_3099554] using wordTrace_append hprefix tailTrace_3099554
  have hstable : (prefixWord ++ tailWord_3099554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099554).length < 2 ^ (prefixWord ++ tailWord_3099554).sum := by decide
  have hdescent : baseEnd_3099554 < baseStart_3099554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099567 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 2, 2, 2]
def baseStart_3099567 : Nat := 118140960795 + 3099567 * 2 ^ 59
def prefixEnd_3099567 : Nat := 4983230072969 + 3 ^ 40 * 3099567 * 2
def baseEnd_3099567 : Nat := 1591567691814579663557857

theorem tailTrace_3099567 : CollatzResearch.WordTrace tailWord_3099567 prefixEnd_3099567 1591567691814579663557857 := by
  unfold tailWord_3099567
  simp only [CollatzResearch.WordTrace]
  refine ⟨113050495961805597743896955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75366997307870398495931303 113050495961805597743896955)
  ·
    refine ⟨169575743942708396615845433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113050495961805597743896955 169575743942708396615845433)
    ·
      refine ⟨127181807957031297461884075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169575743942708396615845433 127181807957031297461884075)
      ·
        refine ⟨190772711935546946192826113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127181807957031297461884075 190772711935546946192826113)
        ·
          refine ⟨143079533951660209644619585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190772711935546946192826113 143079533951660209644619585)
          ·
            refine ⟨107309650463745157233464689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143079533951660209644619585 107309650463745157233464689)
            ·
              refine ⟨80482237847808867925098517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107309650463745157233464689 80482237847808867925098517)
              ·
                refine ⟨3772604899116040683988993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80482237847808867925098517 3772604899116040683988993)
                ·
                  refine ⟨2829453674337030512991745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3772604899116040683988993 2829453674337030512991745)
                  ·
                    refine ⟨2122090255752772884743809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829453674337030512991745 2122090255752772884743809)
                    ·
                      refine ⟨1591567691814579663557857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122090255752772884743809 1591567691814579663557857)
                      ·
                        rfl

theorem cell23_3099567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 2, 2].length) (baseStart_3099567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099567 prefixEnd_3099567 := by exact prefixLift 3099567
  have htrace : WordTrace (prefixWord ++ tailWord_3099567) baseStart_3099567 baseEnd_3099567 := by
    simpa [prefixWord, tailWord_3099567, baseEnd_3099567] using wordTrace_append hprefix tailTrace_3099567
  have hstable : (prefixWord ++ tailWord_3099567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099567).length < 2 ^ (prefixWord ++ tailWord_3099567).sum := by decide
  have hdescent : baseEnd_3099567 < baseStart_3099567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099583 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_3099583 : Nat := 118140960795 + 3099583 * 2 ^ 59
def prefixEnd_3099583 : Nat := 4983230072969 + 3 ^ 40 * 3099583 * 2
def baseEnd_3099583 : Nat := 1591575907505051600957783

theorem tailTrace_3099583 : CollatzResearch.WordTrace tailWord_3099583 prefixEnd_3099583 1591575907505051600957783 := by
  unfold tailWord_3099583
  simp only [CollatzResearch.WordTrace]
  refine ⟨113051079529747632476479403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75367386353165088317652935 113051079529747632476479403)
  ·
    refine ⟨169576619294621448714719105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113051079529747632476479403 169576619294621448714719105)
    ·
      refine ⟨127182464470966086536039329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169576619294621448714719105 127182464470966086536039329)
      ·
        refine ⟨95386848353224564902029497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127182464470966086536039329 95386848353224564902029497)
        ·
          refine ⟨71540136264918423676522123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95386848353224564902029497 71540136264918423676522123)
          ·
            refine ⟨107310204397377635514783185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71540136264918423676522123 107310204397377635514783185)
            ·
              refine ⟨80482653298033226636087389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107310204397377635514783185 80482653298033226636087389)
              ·
                refine ⟨30180994986762459988532771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80482653298033226636087389 30180994986762459988532771)
                ·
                  refine ⟨45271492480143689982799157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30180994986762459988532771 45271492480143689982799157)
                  ·
                    refine ⟨4244202420013470935887421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45271492480143689982799157 4244202420013470935887421)
                    ·
                      refine ⟨1591575907505051600957783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244202420013470935887421 1591575907505051600957783)
                      ·
                        rfl

theorem cell23_3099583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_3099583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099583 prefixEnd_3099583 := by exact prefixLift 3099583
  have htrace : WordTrace (prefixWord ++ tailWord_3099583) baseStart_3099583 baseEnd_3099583 := by
    simpa [prefixWord, tailWord_3099583, baseEnd_3099583] using wordTrace_append hprefix tailTrace_3099583
  have hstable : (prefixWord ++ tailWord_3099583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099583).length < 2 ^ (prefixWord ++ tailWord_3099583).sum := by decide
  have hdescent : baseEnd_3099583 < baseStart_3099583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099640 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 6, 2]
def baseStart_3099640 : Nat := 118140960795 + 3099640 * 2 ^ 59
def prefixEnd_3099640 : Nat := 4983230072969 + 3 ^ 40 * 3099640 * 2
def baseEnd_3099640 : Nat := 1591605175902357877945021

theorem tailTrace_3099640 : CollatzResearch.WordTrace tailWord_3099640 prefixEnd_3099640 1591605175902357877945021 := by
  unfold tailWord_3099640
  simp only [CollatzResearch.WordTrace]
  refine ⟨56526579245270565605652187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75368772327027420807536249 56526579245270565605652187)
  ·
    refine ⟨84789868867905848408478281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56526579245270565605652187 84789868867905848408478281)
    ·
      refine ⟨63592401650929386306358711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84789868867905848408478281 63592401650929386306358711)
      ·
        refine ⟨95388602476394079459538067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63592401650929386306358711 95388602476394079459538067)
        ·
          refine ⟨143082903714591119189307101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95388602476394079459538067 143082903714591119189307101)
          ·
            refine ⟨53656088892971669695990163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143082903714591119189307101 53656088892971669695990163)
            ·
              refine ⟨80484133339457504543985245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53656088892971669695990163 80484133339457504543985245)
              ·
                refine ⟨30181550002296564203994467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80484133339457504543985245 30181550002296564203994467)
                ·
                  refine ⟨45272325003444846305991701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30181550002296564203994467 45272325003444846305991701)
                  ·
                    refine ⟨2122140234536477170593361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45272325003444846305991701 2122140234536477170593361)
                    ·
                      refine ⟨1591605175902357877945021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122140234536477170593361 1591605175902357877945021)
                      ·
                        rfl

theorem cell23_3099640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_3099640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099640 prefixEnd_3099640 := by exact prefixLift 3099640
  have htrace : WordTrace (prefixWord ++ tailWord_3099640) baseStart_3099640 baseEnd_3099640 := by
    simpa [prefixWord, tailWord_3099640, baseEnd_3099640] using wordTrace_append hprefix tailTrace_3099640
  have hstable : (prefixWord ++ tailWord_3099640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099640).length < 2 ^ (prefixWord ++ tailWord_3099640).sum := by decide
  have hdescent : baseEnd_3099640 < baseStart_3099640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099667 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 1, 4]
def baseStart_3099667 : Nat := 118140960795 + 3099667 * 2 ^ 59
def prefixEnd_3099667 : Nat := 4983230072969 + 3 ^ 40 * 3099667 * 2
def baseEnd_3099667 : Nat := 530539679960009757435799

theorem tailTrace_3099667 : CollatzResearch.WordTrace tailWord_3099667 prefixEnd_3099667 530539679960009757435799 := by
  unfold tailWord_3099667
  simp only [CollatzResearch.WordTrace]
  refine ⟨113054143261443314822537255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75369428840962209881691503 113054143261443314822537255)
  ·
    refine ⟨169581214892164972233805883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113054143261443314822537255 169581214892164972233805883)
    ·
      refine ⟨254371822338247458350708825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169581214892164972233805883 254371822338247458350708825)
      ·
        refine ⟨190778866753685593763031619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254371822338247458350708825 190778866753685593763031619)
        ·
          refine ⟨286168300130528390644547429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190778866753685593763031619 286168300130528390644547429)
          ·
            refine ⟨53656556274474073245852643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286168300130528390644547429 53656556274474073245852643)
            ·
              refine ⟨80484834411711109868778965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53656556274474073245852643 80484834411711109868778965)
              ·
                refine ⟨1886363306524479137549507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80484834411711109868778965 1886363306524479137549507)
                ·
                  refine ⟨2829544959786718706324261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886363306524479137549507 2829544959786718706324261)
                  ·
                    refine ⟨530539679960009757435799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2829544959786718706324261 530539679960009757435799)
                    ·
                      rfl

theorem cell23_3099667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 4].length) (baseStart_3099667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099667 prefixEnd_3099667 := by exact prefixLift 3099667
  have htrace : WordTrace (prefixWord ++ tailWord_3099667) baseStart_3099667 baseEnd_3099667 := by
    simpa [prefixWord, tailWord_3099667, baseEnd_3099667] using wordTrace_append hprefix tailTrace_3099667
  have hstable : (prefixWord ++ tailWord_3099667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099667).length < 2 ^ (prefixWord ++ tailWord_3099667).sum := by decide
  have hdescent : baseEnd_3099667 < baseStart_3099667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099703 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3099703 : Nat := 118140960795 + 3099703 * 2 ^ 59
def prefixEnd_3099703 : Nat := 4983230072969 + 3 ^ 40 * 3099703 * 2
def baseEnd_3099703 : Nat := 1591637525183591131457231

theorem tailTrace_3099703 : CollatzResearch.WordTrace tailWord_3099703 prefixEnd_3099703 1591637525183591131457231 := by
  unfold tailWord_3099703
  simp only [CollatzResearch.WordTrace]
  refine ⟨113055456289312892970847763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75370304192875261980565175 113055456289312892970847763)
  ·
    refine ⟨169583184433969339456271645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113055456289312892970847763 169583184433969339456271645)
    ·
      refine ⟨63593694162738502296101867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169583184433969339456271645 63593694162738502296101867)
      ·
        refine ⟨95390541244107753444152801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63593694162738502296101867 95390541244107753444152801)
        ·
          refine ⟨71542905933080815083114601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95390541244107753444152801 71542905933080815083114601)
          ·
            refine ⟨53657179449810611312335951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71542905933080815083114601 53657179449810611312335951)
            ·
              refine ⟨80485769174715916968503927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53657179449810611312335951 80485769174715916968503927)
              ·
                refine ⟨120728653762073875452755891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80485769174715916968503927 120728653762073875452755891)
                ·
                  refine ⟨181092980643110813179133837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120728653762073875452755891 181092980643110813179133837)
                  ·
                    refine ⟨67909867741166554942175189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181092980643110813179133837 67909867741166554942175189)
                    ·
                      refine ⟨1591637525183591131457231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67909867741166554942175189 1591637525183591131457231)
                      ·
                        rfl

theorem cell23_3099703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3099703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099703 prefixEnd_3099703 := by exact prefixLift 3099703
  have htrace : WordTrace (prefixWord ++ tailWord_3099703) baseStart_3099703 baseEnd_3099703 := by
    simpa [prefixWord, tailWord_3099703, baseEnd_3099703] using wordTrace_append hprefix tailTrace_3099703
  have hstable : (prefixWord ++ tailWord_3099703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099703).length < 2 ^ (prefixWord ++ tailWord_3099703).sum := by decide
  have hdescent : baseEnd_3099703 < baseStart_3099703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099718 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3099718 : Nat := 118140960795 + 3099718 * 2 ^ 59
def prefixEnd_3099718 : Nat := 4983230072969 + 3 ^ 40 * 3099718 * 2
def baseEnd_3099718 : Nat := 530548409131136190923221

theorem tailTrace_3099718 : CollatzResearch.WordTrace tailWord_3099718 prefixEnd_3099718 530548409131136190923221 := by
  unfold tailWord_3099718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533000105758079704145119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75370668922839033688429205 3533000105758079704145119)
  ·
    refine ⟨5299500158637119556217679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533000105758079704145119 5299500158637119556217679)
    ·
      refine ⟨7949250237955679334326519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5299500158637119556217679 7949250237955679334326519)
      ·
        refine ⟨11923875356933519001489779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7949250237955679334326519 11923875356933519001489779)
        ·
          refine ⟨17885813035400278502234669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11923875356933519001489779 17885813035400278502234669)
          ·
            refine ⟨6707179888275104438338001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17885813035400278502234669 6707179888275104438338001)
            ·
              refine ⟨5030384916206328328753501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707179888275104438338001 5030384916206328328753501)
              ·
                refine ⟨1886394343577373123282563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5030384916206328328753501 1886394343577373123282563)
                ·
                  refine ⟨2829591515366059684923845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886394343577373123282563 2829591515366059684923845)
                  ·
                    refine ⟨530548409131136190923221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2829591515366059684923845 530548409131136190923221)
                    ·
                      rfl

theorem cell23_3099718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3099718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099718 prefixEnd_3099718 := by exact prefixLift 3099718
  have htrace : WordTrace (prefixWord ++ tailWord_3099718) baseStart_3099718 baseEnd_3099718 := by
    simpa [prefixWord, tailWord_3099718, baseEnd_3099718] using wordTrace_append hprefix tailTrace_3099718
  have hstable : (prefixWord ++ tailWord_3099718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099718).length < 2 ^ (prefixWord ++ tailWord_3099718).sum := by decide
  have hdescent : baseEnd_3099718 < baseStart_3099718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099757 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_3099757 : Nat := 118140960795 + 3099757 * 2 ^ 59
def prefixEnd_3099757 : Nat := 4983230072969 + 3 ^ 40 * 3099757 * 2
def baseEnd_3099757 : Nat := 530555084379644640060661

theorem tailTrace_3099757 : CollatzResearch.WordTrace tailWord_3099757 prefixEnd_3099757 530555084379644640060661 := by
  unfold tailWord_3099757
  simp only [CollatzResearch.WordTrace]
  refine ⟨113057425831117260193313525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75371617220744840128875683 113057425831117260193313525)
  ·
    refine ⟨10599133671667243143123143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113057425831117260193313525 10599133671667243143123143)
    ·
      refine ⟨15898700507500864714684715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599133671667243143123143 15898700507500864714684715)
      ·
        refine ⟨23848050761251297072027073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15898700507500864714684715 23848050761251297072027073)
        ·
          refine ⟨17886038070938472804020305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23848050761251297072027073 17886038070938472804020305)
          ·
            refine ⟨13414528553203854603015229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17886038070938472804020305 13414528553203854603015229)
            ·
              refine ⟨5030448207451445476130711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13414528553203854603015229 5030448207451445476130711)
              ·
                refine ⟨7545672311177168214196067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030448207451445476130711 7545672311177168214196067)
                ·
                  refine ⟨11318508466765752321294101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7545672311177168214196067 11318508466765752321294101)
                  ·
                    refine ⟨530555084379644640060661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11318508466765752321294101 530555084379644640060661)
                    ·
                      rfl

theorem cell23_3099757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_3099757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099757 prefixEnd_3099757 := by exact prefixLift 3099757
  have htrace : WordTrace (prefixWord ++ tailWord_3099757) baseStart_3099757 baseEnd_3099757 := by
    simpa [prefixWord, tailWord_3099757, baseEnd_3099757] using wordTrace_append hprefix tailTrace_3099757
  have hstable : (prefixWord ++ tailWord_3099757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099757).length < 2 ^ (prefixWord ++ tailWord_3099757).sum := by decide
  have hdescent : baseEnd_3099757 < baseStart_3099757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099760 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_3099760 : Nat := 118140960795 + 3099760 * 2 ^ 59
def prefixEnd_3099760 : Nat := 4983230072969 + 3 ^ 40 * 3099760 * 2
def baseEnd_3099760 : Nat := 1591666793580897408444469

theorem tailTrace_3099760 : CollatzResearch.WordTrace tailWord_3099760 prefixEnd_3099760 1591666793580897408444469 := by
  unfold tailWord_3099760
  simp only [CollatzResearch.WordTrace]
  refine ⟨56528767625053195852836367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75371690166737594470448489 56528767625053195852836367)
  ·
    refine ⟨84793151437579793779254551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56528767625053195852836367 84793151437579793779254551)
    ·
      refine ⟨127189727156369690668881827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84793151437579793779254551 127189727156369690668881827)
      ·
        refine ⟨190784590734554536003322741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127189727156369690668881827 190784590734554536003322741)
        ·
          refine ⟨17886055381364487750311507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190784590734554536003322741 17886055381364487750311507)
          ·
            refine ⟨26829083072046731625467261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17886055381364487750311507 26829083072046731625467261)
            ·
              refine ⟨10060906152017524359550223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26829083072046731625467261 10060906152017524359550223)
              ·
                refine ⟨15091359228026286539325335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10060906152017524359550223 15091359228026286539325335)
                ·
                  refine ⟨22637038842039429808988003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15091359228026286539325335 22637038842039429808988003)
                  ·
                    refine ⟨33955558263059144713482005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22637038842039429808988003 33955558263059144713482005)
                    ·
                      refine ⟨1591666793580897408444469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33955558263059144713482005 1591666793580897408444469)
                      ·
                        rfl

theorem cell23_3099760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_3099760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099760 prefixEnd_3099760 := by exact prefixLift 3099760
  have htrace : WordTrace (prefixWord ++ tailWord_3099760) baseStart_3099760 baseEnd_3099760 := by
    simpa [prefixWord, tailWord_3099760, baseEnd_3099760] using wordTrace_append hprefix tailTrace_3099760
  have hstable : (prefixWord ++ tailWord_3099760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099760).length < 2 ^ (prefixWord ++ tailWord_3099760).sum := by decide
  have hdescent : baseEnd_3099760 < baseStart_3099760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099784 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3099784 : Nat := 118140960795 + 3099784 * 2 ^ 59
def prefixEnd_3099784 : Nat := 4983230072969 + 3 ^ 40 * 3099784 * 2
def baseEnd_3099784 : Nat := 1591679117116605314544359

theorem tailTrace_3099784 : CollatzResearch.WordTrace tailWord_3099784 prefixEnd_3099784 1591679117116605314544359 := by
  unfold tailWord_3099784
  simp only [CollatzResearch.WordTrace]
  refine ⟨56529205301009721902273203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75372273734679629203030937 56529205301009721902273203)
  ·
    refine ⟨84793807951514582853409805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56529205301009721902273203 84793807951514582853409805)
    ·
      refine ⟨31797677981817968570028677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84793807951514582853409805 31797677981817968570028677)
      ·
        refine ⟨5962064621590869106880377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31797677981817968570028677 5962064621590869106880377)
        ·
          refine ⟨4471548466193151830160283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5962064621590869106880377 4471548466193151830160283)
          ·
            refine ⟨6707322699289727745240425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471548466193151830160283 6707322699289727745240425)
            ·
              refine ⟨5030492024467295808930319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707322699289727745240425 5030492024467295808930319)
              ·
                refine ⟨7545738036700943713395479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030492024467295808930319 7545738036700943713395479)
                ·
                  refine ⟨11318607055051415570093219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7545738036700943713395479 11318607055051415570093219)
                  ·
                    refine ⟨16977910582577123355139829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11318607055051415570093219 16977910582577123355139829)
                    ·
                      refine ⟨1591679117116605314544359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16977910582577123355139829 1591679117116605314544359)
                      ·
                        rfl

theorem cell23_3099784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3099784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099784 prefixEnd_3099784 := by exact prefixLift 3099784
  have htrace : WordTrace (prefixWord ++ tailWord_3099784) baseStart_3099784 baseEnd_3099784 := by
    simpa [prefixWord, tailWord_3099784, baseEnd_3099784] using wordTrace_append hprefix tailTrace_3099784
  have hstable : (prefixWord ++ tailWord_3099784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099784).length < 2 ^ (prefixWord ++ tailWord_3099784).sum := by decide
  have hdescent : baseEnd_3099784 < baseStart_3099784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099818 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3099818 : Nat := 118140960795 + 3099818 * 2 ^ 59
def prefixEnd_3099818 : Nat := 4983230072969 + 3 ^ 40 * 3099818 * 2
def baseEnd_3099818 : Nat := 1591696575458858181519203

theorem tailTrace_3099818 : CollatzResearch.WordTrace tailWord_3099818 prefixEnd_3099818 1591696575458858181519203 := by
  unfold tailWord_3099818
  simp only [CollatzResearch.WordTrace]
  refine ⟨28264912670974066902821027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75373100455930845074189405 28264912670974066902821027)
  ·
    refine ⟨42397369006461100354231541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28264912670974066902821027 42397369006461100354231541)
    ·
      refine ⟨3974753344355728158209207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42397369006461100354231541 3974753344355728158209207)
      ·
        refine ⟨5962130016533592237313811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3974753344355728158209207 5962130016533592237313811)
        ·
          refine ⟨8943195024800388355970717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5962130016533592237313811 8943195024800388355970717)
          ·
            refine ⟨3353698134300145633489019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8943195024800388355970717 3353698134300145633489019)
            ·
              refine ⟨5030547201450218450233529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353698134300145633489019 5030547201450218450233529)
              ·
                refine ⟨3772910401087663837675147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030547201450218450233529 3772910401087663837675147)
                ·
                  refine ⟨5659365601631495756512721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772910401087663837675147 5659365601631495756512721)
                  ·
                    refine ⟨4244524201223621817384541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5659365601631495756512721 4244524201223621817384541)
                    ·
                      refine ⟨1591696575458858181519203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244524201223621817384541 1591696575458858181519203)
                      ·
                        rfl

theorem cell23_3099818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3099818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099818 prefixEnd_3099818 := by exact prefixLift 3099818
  have htrace : WordTrace (prefixWord ++ tailWord_3099818) baseStart_3099818 baseEnd_3099818 := by
    simpa [prefixWord, tailWord_3099818, baseEnd_3099818] using wordTrace_append hprefix tailTrace_3099818
  have hstable : (prefixWord ++ tailWord_3099818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099818).length < 2 ^ (prefixWord ++ tailWord_3099818).sum := by decide
  have hdescent : baseEnd_3099818 < baseStart_3099818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099820 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3099820 : Nat := 118140960795 + 3099820 * 2 ^ 59
def prefixEnd_3099820 : Nat := 4983230072969 + 3 ^ 40 * 3099820 * 2
def baseEnd_3099820 : Nat := 1591697602420167173694193

theorem tailTrace_3099820 : CollatzResearch.WordTrace tailWord_3099820 prefixEnd_3099820 1591697602420167173694193 := by
  unfold tailWord_3099820
  simp only [CollatzResearch.WordTrace]
  refine ⟨56529861814944510976428457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75373149086592681301904609 56529861814944510976428457)
  ·
    refine ⟨42397396361208383232321343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56529861814944510976428457 42397396361208383232321343)
    ·
      refine ⟨63596094541812574848482015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42397396361208383232321343 63596094541812574848482015)
      ·
        refine ⟨95394141812718862272723023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63596094541812574848482015 95394141812718862272723023)
        ·
          refine ⟨143091212719078293409084535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95394141812718862272723023 143091212719078293409084535)
          ·
            refine ⟨214636819078617440113626803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143091212719078293409084535 214636819078617440113626803)
            ·
              refine ⟨321955228617926160170440205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214636819078617440113626803 321955228617926160170440205)
              ·
                refine ⟨120733210731722310063915077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321955228617926160170440205 120733210731722310063915077)
                ·
                  refine ⟨22637477012197933136984077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120733210731722310063915077 22637477012197933136984077)
                  ·
                    refine ⟨8489053879574224926369029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22637477012197933136984077 8489053879574224926369029)
                    ·
                      refine ⟨1591697602420167173694193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8489053879574224926369029 1591697602420167173694193)
                      ·
                        rfl

theorem cell23_3099820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3099820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099820 prefixEnd_3099820 := by exact prefixLift 3099820
  have htrace : WordTrace (prefixWord ++ tailWord_3099820) baseStart_3099820 baseEnd_3099820 := by
    simpa [prefixWord, tailWord_3099820, baseEnd_3099820] using wordTrace_append hprefix tailTrace_3099820
  have hstable : (prefixWord ++ tailWord_3099820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099820).length < 2 ^ (prefixWord ++ tailWord_3099820).sum := by decide
  have hdescent : baseEnd_3099820 < baseStart_3099820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099871 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 2, 2, 2]
def baseStart_3099871 : Nat := 118140960795 + 3099871 * 2 ^ 59
def prefixEnd_3099871 : Nat := 4983230072969 + 3 ^ 40 * 3099871 * 2
def baseEnd_3099871 : Nat := 1591723789933546474156459

theorem tailTrace_3099871 : CollatzResearch.WordTrace tailWord_3099871 prefixEnd_3099871 1591723789933546474156459 := by
  unfold tailWord_3099871
  simp only [CollatzResearch.WordTrace]
  refine ⟨113061583752704257662963467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75374389168469505108642311 113061583752704257662963467)
  ·
    refine ⟨169592375629056386494445201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113061583752704257662963467 169592375629056386494445201)
    ·
      refine ⟨127194281721792289870833901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169592375629056386494445201 127194281721792289870833901)
      ·
        refine ⟨47697855645672108701562713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127194281721792289870833901 47697855645672108701562713)
        ·
          refine ⟨35773391734254081526172035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47697855645672108701562713 35773391734254081526172035)
          ·
            refine ⟨53660087601381122289258053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35773391734254081526172035 53660087601381122289258053)
            ·
              refine ⟨10061266425258960429235885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53660087601381122289258053 10061266425258960429235885)
              ·
                refine ⟨3772974909472110160963457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10061266425258960429235885 3772974909472110160963457)
                ·
                  refine ⟨2829731182104082620722593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3772974909472110160963457 2829731182104082620722593)
                  ·
                    refine ⟨2122298386578061965541945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829731182104082620722593 2122298386578061965541945)
                    ·
                      refine ⟨1591723789933546474156459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122298386578061965541945 1591723789933546474156459)
                      ·
                        rfl

theorem cell23_3099871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_3099871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099871 prefixEnd_3099871 := by exact prefixLift 3099871
  have htrace : WordTrace (prefixWord ++ tailWord_3099871) baseStart_3099871 baseEnd_3099871 := by
    simpa [prefixWord, tailWord_3099871, baseEnd_3099871] using wordTrace_append hprefix tailTrace_3099871
  have hstable : (prefixWord ++ tailWord_3099871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099871).length < 2 ^ (prefixWord ++ tailWord_3099871).sum := by decide
  have hdescent : baseEnd_3099871 < baseStart_3099871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099892 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3099892 : Nat := 118140960795 + 3099892 * 2 ^ 59
def prefixEnd_3099892 : Nat := 4983230072969 + 3 ^ 40 * 3099892 * 2
def baseEnd_3099892 : Nat := 1591734573027290891993863

theorem tailTrace_3099892 : CollatzResearch.WordTrace tailWord_3099892 prefixEnd_3099892 1591734573027290891993863 := by
  unfold tailWord_3099892
  simp only [CollatzResearch.WordTrace]
  refine ⟨56531174842814089124738965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75374899790418785499651953 56531174842814089124738965)
  ·
    refine ⟨2649898820756910427722139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56531174842814089124738965 2649898820756910427722139)
    ·
      refine ⟨3974848231135365641583209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2649898820756910427722139 3974848231135365641583209)
      ·
        refine ⟨2981136173351524231187407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3974848231135365641583209 2981136173351524231187407)
        ·
          refine ⟨4471704260027286346781111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981136173351524231187407 4471704260027286346781111)
          ·
            refine ⟨6707556390040929520171667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471704260027286346781111 6707556390040929520171667)
            ·
              refine ⟨10061334585061394280257501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6707556390040929520171667 10061334585061394280257501)
              ·
                refine ⟨3773000469398022855096563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10061334585061394280257501 3773000469398022855096563)
                ·
                  refine ⟨5659500704097034282644845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773000469398022855096563 5659500704097034282644845)
                  ·
                    refine ⟨2122312764036387855991817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5659500704097034282644845 2122312764036387855991817)
                    ·
                      refine ⟨1591734573027290891993863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122312764036387855991817 1591734573027290891993863)
                      ·
                        rfl

theorem cell23_3099892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3099892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099892 prefixEnd_3099892 := by exact prefixLift 3099892
  have htrace : WordTrace (prefixWord ++ tailWord_3099892) baseStart_3099892 baseEnd_3099892 := by
    simpa [prefixWord, tailWord_3099892, baseEnd_3099892] using wordTrace_append hprefix tailTrace_3099892
  have hstable : (prefixWord ++ tailWord_3099892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099892).length < 2 ^ (prefixWord ++ tailWord_3099892).sum := by decide
  have hdescent : baseEnd_3099892 < baseStart_3099892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099922 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3099922 : Nat := 118140960795 + 3099922 * 2 ^ 59
def prefixEnd_3099922 : Nat := 4983230072969 + 3 ^ 40 * 3099922 * 2
def baseEnd_3099922 : Nat := 1591749977446925774618725

theorem tailTrace_3099922 : CollatzResearch.WordTrace tailWord_3099922 prefixEnd_3099922 1591749977446925774618725 := by
  unfold tailWord_3099922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265860968879873343267505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75375629250346328915380013 28265860968879873343267505)
  ·
    refine ⟨21199395726659905007450629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28265860968879873343267505 21199395726659905007450629)
    ·
      refine ⟨3974886698748732188896993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21199395726659905007450629 3974886698748732188896993)
      ·
        refine ⟨2981165024061549141672745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3974886698748732188896993 2981165024061549141672745)
        ·
          refine ⟨2235873768046161856254559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981165024061549141672745 2235873768046161856254559)
          ·
            refine ⟨3353810652069242784381839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235873768046161856254559 3353810652069242784381839)
            ·
              refine ⟨5030715978103864176572759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353810652069242784381839 5030715978103864176572759)
              ·
                refine ⟨7546073967155796264859139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030715978103864176572759 7546073967155796264859139)
                ·
                  refine ⟨11319110950733694397288709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546073967155796264859139 11319110950733694397288709)
                  ·
                    refine ⟨2122333303262567699491633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11319110950733694397288709 2122333303262567699491633)
                    ·
                      refine ⟨1591749977446925774618725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122333303262567699491633 1591749977446925774618725)
                      ·
                        rfl

theorem cell23_3099922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3099922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099922 prefixEnd_3099922 := by exact prefixLift 3099922
  have htrace : WordTrace (prefixWord ++ tailWord_3099922) baseStart_3099922 baseEnd_3099922 := by
    simpa [prefixWord, tailWord_3099922, baseEnd_3099922] using wordTrace_append hprefix tailTrace_3099922
  have hstable : (prefixWord ++ tailWord_3099922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099922).length < 2 ^ (prefixWord ++ tailWord_3099922).sum := by decide
  have hdescent : baseEnd_3099922 < baseStart_3099922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099927 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3099927 : Nat := 118140960795 + 3099927 * 2 ^ 59
def prefixEnd_3099927 : Nat := 4983230072969 + 3 ^ 40 * 3099927 * 2
def baseEnd_3099927 : Nat := 1591752544850198255056201

theorem tailTrace_3099927 : CollatzResearch.WordTrace tailWord_3099927 prefixEnd_3099927 1591752544850198255056201 := by
  unfold tailWord_3099927
  simp only [CollatzResearch.WordTrace]
  refine ⟨113063626240501379227002035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75375750827000919484668023 113063626240501379227002035)
  ·
    refine ⟨169595439360752068840503053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113063626240501379227002035 169595439360752068840503053)
    ·
      refine ⟨63598289760282025815188645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169595439360752068840503053 63598289760282025815188645)
      ·
        refine ⟨11924679330052879840347871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63598289760282025815188645 11924679330052879840347871)
        ·
          refine ⟨17887018995079319760521807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11924679330052879840347871 17887018995079319760521807)
          ·
            refine ⟨26830528492618979640782711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17887018995079319760521807 26830528492618979640782711)
            ·
              refine ⟨40245792738928469461174067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26830528492618979640782711 40245792738928469461174067)
              ·
                refine ⟨60368689108392704191761101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40245792738928469461174067 60368689108392704191761101)
                ·
                  refine ⟨22638258415647264071910413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60368689108392704191761101 22638258415647264071910413)
                  ·
                    refine ⟨8489346905867724026966405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22638258415647264071910413 8489346905867724026966405)
                    ·
                      refine ⟨1591752544850198255056201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8489346905867724026966405 1591752544850198255056201)
                      ·
                        rfl

theorem cell23_3099927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3099927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099927 prefixEnd_3099927 := by exact prefixLift 3099927
  have htrace : WordTrace (prefixWord ++ tailWord_3099927) baseStart_3099927 baseEnd_3099927 := by
    simpa [prefixWord, tailWord_3099927, baseEnd_3099927] using wordTrace_append hprefix tailTrace_3099927
  have hstable : (prefixWord ++ tailWord_3099927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099927).length < 2 ^ (prefixWord ++ tailWord_3099927).sum := by decide
  have hdescent : baseEnd_3099927 < baseStart_3099927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099944 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3099944 : Nat := 118140960795 + 3099944 * 2 ^ 59
def prefixEnd_3099944 : Nat := 4983230072969 + 3 ^ 40 * 3099944 * 2
def baseEnd_3099944 : Nat := 1591761274021324688543623

theorem tailTrace_3099944 : CollatzResearch.WordTrace tailWord_3099944 prefixEnd_3099944 1591761274021324688543623 := by
  unfold tailWord_3099944
  simp only [CollatzResearch.WordTrace]
  refine ⟨56532123140719895565185443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75376164187626527420247257 56532123140719895565185443)
  ·
    refine ⟨84798184711079843347778165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56532123140719895565185443 84798184711079843347778165)
    ·
      refine ⟨7949829816663735313854203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84798184711079843347778165 7949829816663735313854203)
      ·
        refine ⟨11924744724995602970781305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7949829816663735313854203 11924744724995602970781305)
        ·
          refine ⟨8943558543746702228085979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11924744724995602970781305 8943558543746702228085979)
          ·
            refine ⟨13415337815620053342128969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8943558543746702228085979 13415337815620053342128969)
            ·
              refine ⟨10061503361715040006596727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13415337815620053342128969 10061503361715040006596727)
              ·
                refine ⟨15092255042572560009895091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061503361715040006596727 15092255042572560009895091)
                ·
                  refine ⟨22638382563858840014842637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15092255042572560009895091 22638382563858840014842637)
                  ·
                    refine ⟨8489393461447065005565989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22638382563858840014842637 8489393461447065005565989)
                    ·
                      refine ⟨1591761274021324688543623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8489393461447065005565989 1591761274021324688543623)
                      ·
                        rfl

theorem cell23_3099944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3099944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099944 prefixEnd_3099944 := by exact prefixLift 3099944
  have htrace : WordTrace (prefixWord ++ tailWord_3099944) baseStart_3099944 baseEnd_3099944 := by
    simpa [prefixWord, tailWord_3099944, baseEnd_3099944] using wordTrace_append hprefix tailTrace_3099944
  have hstable : (prefixWord ++ tailWord_3099944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099944).length < 2 ^ (prefixWord ++ tailWord_3099944).sum := by decide
  have hdescent : baseEnd_3099944 < baseStart_3099944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099958 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3099958 : Nat := 118140960795 + 3099958 * 2 ^ 59
def prefixEnd_3099958 : Nat := 4983230072969 + 3 ^ 40 * 3099958 * 2
def baseEnd_3099958 : Nat := 530589487583495877922853

theorem tailTrace_3099958 : CollatzResearch.WordTrace tailWord_3099958 prefixEnd_3099958 530589487583495877922853 := by
  unfold tailWord_3099958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066547306461816970086283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75376504602259381014253685 7066547306461816970086283)
  ·
    refine ⟨10599820959692725455129425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7066547306461816970086283 10599820959692725455129425)
    ·
      refine ⟨7949865719769544091347069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10599820959692725455129425 7949865719769544091347069)
      ·
        refine ⟨2981199644913579034255151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7949865719769544091347069 2981199644913579034255151)
        ·
          refine ⟨4471799467370368551382727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981199644913579034255151 4471799467370368551382727)
          ·
            refine ⟨6707699201055552827074091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471799467370368551382727 6707699201055552827074091)
            ·
              refine ⟨10061548801583329240611137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6707699201055552827074091 10061548801583329240611137)
              ·
                refine ⟨7546161601187496930458353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10061548801583329240611137 7546161601187496930458353)
                ·
                  refine ⟨5659621200890622697843765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546161601187496930458353 5659621200890622697843765)
                  ·
                    refine ⟨530589487583495877922853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5659621200890622697843765 530589487583495877922853)
                    ·
                      rfl

theorem cell23_3099958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3099958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099958 prefixEnd_3099958 := by exact prefixLift 3099958
  have htrace : WordTrace (prefixWord ++ tailWord_3099958) baseStart_3099958 baseEnd_3099958 := by
    simpa [prefixWord, tailWord_3099958, baseEnd_3099958] using wordTrace_append hprefix tailTrace_3099958
  have hstable : (prefixWord ++ tailWord_3099958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099958).length < 2 ^ (prefixWord ++ tailWord_3099958).sum := by decide
  have hdescent : baseEnd_3099958 < baseStart_3099958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099961 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3099961 : Nat := 118140960795 + 3099961 * 2 ^ 59
def prefixEnd_3099961 : Nat := 4983230072969 + 3 ^ 40 * 3099961 * 2
def baseEnd_3099961 : Nat := 1591770003192451122031045

theorem tailTrace_3099961 : CollatzResearch.WordTrace tailWord_3099961 prefixEnd_3099961 1591770003192451122031045 := by
  unfold tailWord_3099961
  simp only [CollatzResearch.WordTrace]
  refine ⟨113064866322378203033739737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75376577548252135355826491 113064866322378203033739737)
  ·
    refine ⟨84798649741783652275304803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113064866322378203033739737 84798649741783652275304803)
    ·
      refine ⟨127197974612675478412957205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84798649741783652275304803 127197974612675478412957205)
      ·
        refine ⟨5962405059969163050607369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127197974612675478412957205 5962405059969163050607369)
        ·
          refine ⟨4471803794976872287955527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5962405059969163050607369 4471803794976872287955527)
          ·
            refine ⟨6707705692465308431933291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471803794976872287955527 6707705692465308431933291)
            ·
              refine ⟨10061558538697962647899937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6707705692465308431933291 10061558538697962647899937)
              ·
                refine ⟨7546168904023471985924953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10061558538697962647899937 7546168904023471985924953)
                ·
                  refine ⟨5659626678017603989443715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546168904023471985924953 5659626678017603989443715)
                  ·
                    refine ⟨8489440017026405984165573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5659626678017603989443715 8489440017026405984165573)
                    ·
                      refine ⟨1591770003192451122031045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8489440017026405984165573 1591770003192451122031045)
                      ·
                        rfl

theorem cell23_3099961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3099961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099961 prefixEnd_3099961 := by exact prefixLift 3099961
  have htrace : WordTrace (prefixWord ++ tailWord_3099961) baseStart_3099961 baseEnd_3099961 := by
    simpa [prefixWord, tailWord_3099961, baseEnd_3099961] using wordTrace_append hprefix tailTrace_3099961
  have hstable : (prefixWord ++ tailWord_3099961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099961).length < 2 ^ (prefixWord ++ tailWord_3099961).sum := by decide
  have hdescent : baseEnd_3099961 < baseStart_3099961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099964 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_3099964 : Nat := 118140960795 + 3099964 * 2 ^ 59
def prefixEnd_3099964 : Nat := 4983230072969 + 3 ^ 40 * 3099964 * 2
def baseEnd_3099964 : Nat := 1591771543634414610293531

theorem tailTrace_3099964 : CollatzResearch.WordTrace tailWord_3099964 prefixEnd_3099964 1591771543634414610293531 := by
  unfold tailWord_3099964
  simp only [CollatzResearch.WordTrace]
  refine ⟨56532487870683667273049473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75376650494244889697399297 56532487870683667273049473)
  ·
    refine ⟨42399365903012750454787105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56532487870683667273049473 42399365903012750454787105)
    ·
      refine ⟨31799524427259562841090329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42399365903012750454787105 31799524427259562841090329)
      ·
        refine ⟨23849643320444672130817747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31799524427259562841090329 23849643320444672130817747)
        ·
          refine ⟨35774464980667008196226621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23849643320444672130817747 35774464980667008196226621)
          ·
            refine ⟨13415424367750128073584983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35774464980667008196226621 13415424367750128073584983)
            ·
              refine ⟨20123136551625192110377475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13415424367750128073584983 20123136551625192110377475)
              ·
                refine ⟨30184704827437788165566213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20123136551625192110377475 30184704827437788165566213)
                ·
                  refine ⟨5659632155144585281043665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30184704827437788165566213 5659632155144585281043665)
                  ·
                    refine ⟨4244724116358438960782749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5659632155144585281043665 4244724116358438960782749)
                    ·
                      refine ⟨1591771543634414610293531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244724116358438960782749 1591771543634414610293531)
                      ·
                        rfl

theorem cell23_3099964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_3099964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099964 prefixEnd_3099964 := by exact prefixLift 3099964
  have htrace : WordTrace (prefixWord ++ tailWord_3099964) baseStart_3099964 baseEnd_3099964 := by
    simpa [prefixWord, tailWord_3099964, baseEnd_3099964] using wordTrace_append hprefix tailTrace_3099964
  have hstable : (prefixWord ++ tailWord_3099964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099964).length < 2 ^ (prefixWord ++ tailWord_3099964).sum := by decide
  have hdescent : baseEnd_3099964 < baseStart_3099964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099967 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 8]
def baseStart_3099967 : Nat := 118140960795 + 3099967 * 2 ^ 59
def prefixEnd_3099967 : Nat := 4983230072969 + 3 ^ 40 * 3099967 * 2
def baseEnd_3099967 : Nat := 176863676008486455395113

theorem tailTrace_3099967 : CollatzResearch.WordTrace tailWord_3099967 prefixEnd_3099967 176863676008486455395113 := by
  unfold tailWord_3099967
  simp only [CollatzResearch.WordTrace]
  refine ⟨113065085160356466058458155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75376723440237644038972103 113065085160356466058458155)
  ·
    refine ⟨169597627740534699087687233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113065085160356466058458155 169597627740534699087687233)
    ·
      refine ⟨127198220805401024315765425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169597627740534699087687233 127198220805401024315765425)
      ·
        refine ⟨95398665604050768236824069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127198220805401024315765425 95398665604050768236824069)
        ·
          refine ⟨17887249800759519044404513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95398665604050768236824069 17887249800759519044404513)
          ·
            refine ⟨13415437350569639283303385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17887249800759519044404513 13415437350569639283303385)
            ·
              refine ⟨10061578012927229462477539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13415437350569639283303385 10061578012927229462477539)
              ·
                refine ⟨15092367019390844193716309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061578012927229462477539 15092367019390844193716309)
                ·
                  refine ⟨176863676008486455395113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15092367019390844193716309 176863676008486455395113)
                  ·
                    rfl

theorem cell23_3099967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 8].length) (baseStart_3099967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3099967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3099967 prefixEnd_3099967 := by exact prefixLift 3099967
  have htrace : WordTrace (prefixWord ++ tailWord_3099967) baseStart_3099967 baseEnd_3099967 := by
    simpa [prefixWord, tailWord_3099967, baseEnd_3099967] using wordTrace_append hprefix tailTrace_3099967
  have hstable : (prefixWord ++ tailWord_3099967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099967).length < 2 ^ (prefixWord ++ tailWord_3099967).sum := by decide
  have hdescent : baseEnd_3099967 < baseStart_3099967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100027 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 3, 6]
def baseStart_3100027 : Nat := 118140960795 + 3100027 * 2 ^ 59
def prefixEnd_3100027 : Nat := 4983230072969 + 3 ^ 40 * 3100027 * 2
def baseEnd_3100027 : Nat := 530601297638549287935247

theorem tailTrace_3100027 : CollatzResearch.WordTrace tailWord_3100027 prefixEnd_3100027 530601297638549287935247 := by
  unfold tailWord_3100027
  simp only [CollatzResearch.WordTrace]
  refine ⟨113067273540139096305642335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75378182360092730870428223 113067273540139096305642335)
  ·
    refine ⟨169600910310208644458463503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113067273540139096305642335 169600910310208644458463503)
    ·
      refine ⟨254401365465312966687695255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169600910310208644458463503 254401365465312966687695255)
      ·
        refine ⟨381602048197969450031542883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254401365465312966687695255 381602048197969450031542883)
        ·
          refine ⟨572403072296954175047314325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381602048197969450031542883 572403072296954175047314325)
          ·
            refine ⟨26831394013919726955342859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 572403072296954175047314325 26831394013919726955342859)
            ·
              refine ⟨40247091020879590433014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26831394013919726955342859 40247091020879590433014289)
              ·
                refine ⟨30185318265659692824760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40247091020879590433014289 30185318265659692824760717)
                ·
                  refine ⟨11319494349622384809285269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30185318265659692824760717 11319494349622384809285269)
                  ·
                    refine ⟨530601297638549287935247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11319494349622384809285269 530601297638549287935247)
                    ·
                      rfl

theorem cell23_3100027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_3100027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100027 prefixEnd_3100027 := by exact prefixLift 3100027
  have htrace : WordTrace (prefixWord ++ tailWord_3100027) baseStart_3100027 baseEnd_3100027 := by
    simpa [prefixWord, tailWord_3100027, baseEnd_3100027] using wordTrace_append hprefix tailTrace_3100027
  have hstable : (prefixWord ++ tailWord_3100027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100027).length < 2 ^ (prefixWord ++ tailWord_3100027).sum := by decide
  have hdescent : baseEnd_3100027 < baseStart_3100027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100028 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_3100028 : Nat := 118140960795 + 3100028 * 2 ^ 59
def prefixEnd_3100028 : Nat := 4983230072969 + 3 ^ 40 * 3100028 * 2
def baseEnd_3100028 : Nat := 1591804406396302359893237

theorem tailTrace_3100028 : CollatzResearch.WordTrace tailWord_3100028 prefixEnd_3100028 1591804406396302359893237 := by
  unfold tailWord_3100028
  simp only [CollatzResearch.WordTrace]
  refine ⟨56533655006567736738214369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75378206675423648984285825 56533655006567736738214369)
  ·
    refine ⟨42400241254925802553660777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56533655006567736738214369 42400241254925802553660777)
    ·
      refine ⟨31800180941194351915245583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42400241254925802553660777 31800180941194351915245583)
      ·
        refine ⟨47700271411791527872868375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31800180941194351915245583 47700271411791527872868375)
        ·
          refine ⟨71550407117687291809302563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47700271411791527872868375 71550407117687291809302563)
          ·
            refine ⟨107325610676530937713953845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71550407117687291809302563 107325610676530937713953845)
            ·
              refine ⟨10061776000924775410683173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107325610676530937713953845 10061776000924775410683173)
              ·
                refine ⟨1886583000173395389503095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10061776000924775410683173 1886583000173395389503095)
                ·
                  refine ⟨2829874500260093084254643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886583000173395389503095 2829874500260093084254643)
                  ·
                    refine ⟨4244811750390139626381965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2829874500260093084254643 4244811750390139626381965)
                    ·
                      refine ⟨1591804406396302359893237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4244811750390139626381965 1591804406396302359893237)
                      ·
                        rfl

theorem cell23_3100028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_3100028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100028 prefixEnd_3100028 := by exact prefixLift 3100028
  have htrace : WordTrace (prefixWord ++ tailWord_3100028) baseStart_3100028 baseEnd_3100028 := by
    simpa [prefixWord, tailWord_3100028, baseEnd_3100028] using wordTrace_append hprefix tailTrace_3100028
  have hstable : (prefixWord ++ tailWord_3100028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100028).length < 2 ^ (prefixWord ++ tailWord_3100028).sum := by decide
  have hdescent : baseEnd_3100028 < baseStart_3100028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100044 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_3100044 : Nat := 118140960795 + 3100044 * 2 ^ 59
def prefixEnd_3100044 : Nat := 4983230072969 + 3 ^ 40 * 3100044 * 2
def baseEnd_3100044 : Nat := 530604207362258099097721

theorem tailTrace_3100044 : CollatzResearch.WordTrace tailWord_3100044 prefixEnd_3100044 530604207362258099097721 := by
  unfold tailWord_3100044
  simp only [CollatzResearch.WordTrace]
  refine ⟨56533946790538754104505593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75378595720718338806007457 56533946790538754104505593)
  ·
    refine ⟨42400460092904065578379195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56533946790538754104505593 42400460092904065578379195)
    ·
      refine ⟨63600690139356098367568793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42400460092904065578379195 63600690139356098367568793)
      ·
        refine ⟨47700517604517073775676595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63600690139356098367568793 47700517604517073775676595)
        ·
          refine ⟨71550776406775610663514893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47700517604517073775676595 71550776406775610663514893)
          ·
            refine ⟨26831541152540853998818085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71550776406775610663514893 26831541152540853998818085)
            ·
              refine ⟨5030913966101410124778391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26831541152540853998818085 5030913966101410124778391)
              ·
                refine ⟨7546370949152115187167587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030913966101410124778391 7546370949152115187167587)
                ·
                  refine ⟨11319556423728172780751381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546370949152115187167587 11319556423728172780751381)
                  ·
                    refine ⟨530604207362258099097721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11319556423728172780751381 530604207362258099097721)
                    ·
                      rfl

theorem cell23_3100044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_3100044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100044 prefixEnd_3100044 := by exact prefixLift 3100044
  have htrace : WordTrace (prefixWord ++ tailWord_3100044) baseStart_3100044 baseEnd_3100044 := by
    simpa [prefixWord, tailWord_3100044, baseEnd_3100044] using wordTrace_append hprefix tailTrace_3100044
  have hstable : (prefixWord ++ tailWord_3100044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100044).length < 2 ^ (prefixWord ++ tailWord_3100044).sum := by decide
  have hdescent : baseEnd_3100044 < baseStart_3100044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100064 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3100064 : Nat := 118140960795 + 3100064 * 2 ^ 59
def prefixEnd_3100064 : Nat := 4983230072969 + 3 ^ 40 * 3100064 * 2
def baseEnd_3100064 : Nat := 1591822891699864219043071

theorem tailTrace_3100064 : CollatzResearch.WordTrace tailWord_3100064 prefixEnd_3100064 1591822891699864219043071 := by
  unfold tailWord_3100064
  simp only [CollatzResearch.WordTrace]
  refine ⟨56534311520502525812369623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75379082027336701083159497 56534311520502525812369623)
  ·
    refine ⟨84801467280753788718554435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56534311520502525812369623 84801467280753788718554435)
    ·
      refine ⟨127202200921130683077831653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84801467280753788718554435 127202200921130683077831653)
      ·
        refine ⟨23850412672712003077093435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127202200921130683077831653 23850412672712003077093435)
        ·
          refine ⟨35775619009068004615640153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23850412672712003077093435 35775619009068004615640153)
          ·
            refine ⟨26831714256801003461730115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35775619009068004615640153 26831714256801003461730115)
            ·
              refine ⟨40247571385201505192595173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26831714256801003461730115 40247571385201505192595173)
              ·
                refine ⟨7546419634725282223611595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40247571385201505192595173 7546419634725282223611595)
                ·
                  refine ⟨11319629452087923335417393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546419634725282223611595 11319629452087923335417393)
                  ·
                    refine ⟨8489722089065942501563045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11319629452087923335417393 8489722089065942501563045)
                    ·
                      refine ⟨1591822891699864219043071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8489722089065942501563045 1591822891699864219043071)
                      ·
                        rfl

theorem cell23_3100064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3100064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100064 prefixEnd_3100064 := by exact prefixLift 3100064
  have htrace : WordTrace (prefixWord ++ tailWord_3100064) baseStart_3100064 baseEnd_3100064 := by
    simpa [prefixWord, tailWord_3100064, baseEnd_3100064] using wordTrace_append hprefix tailTrace_3100064
  have hstable : (prefixWord ++ tailWord_3100064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100064).length < 2 ^ (prefixWord ++ tailWord_3100064).sum := by decide
  have hdescent : baseEnd_3100064 < baseStart_3100064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100085 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_3100085 : Nat := 118140960795 + 3100085 * 2 ^ 59
def prefixEnd_3100085 : Nat := 4983230072969 + 3 ^ 40 * 3100085 * 2
def baseEnd_3100085 : Nat := 1591833674793608636880475

theorem tailTrace_3100085 : CollatzResearch.WordTrace tailWord_3100085 prefixEnd_3100085 1591833674793608636880475 := by
  unfold tailWord_3100085
  simp only [CollatzResearch.WordTrace]
  refine ⟨113069388973928972211253709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75379592649285981474169139 113069388973928972211253709)
  ·
    refine ⟨42401020865223364579220141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113069388973928972211253709 42401020865223364579220141)
    ·
      refine ⟨15900382824458761717207553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42401020865223364579220141 15900382824458761717207553)
      ·
        refine ⟨11925287118344071287905665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15900382824458761717207553 11925287118344071287905665)
        ·
          refine ⟨8943965338758053465929249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11925287118344071287905665 8943965338758053465929249)
          ·
            refine ⟨6707974004068540099446937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8943965338758053465929249 6707974004068540099446937)
            ·
              refine ⟨5030980503051405074585203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707974004068540099446937 5030980503051405074585203)
              ·
                refine ⟨7546470754577107611877805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030980503051405074585203 7546470754577107611877805)
                ·
                  refine ⟨2829926532966415354454177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7546470754577107611877805 2829926532966415354454177)
                  ·
                    refine ⟨2122444899724811515840633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2829926532966415354454177 2122444899724811515840633)
                    ·
                      refine ⟨1591833674793608636880475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122444899724811515840633 1591833674793608636880475)
                      ·
                        rfl

theorem cell23_3100085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_3100085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100085 prefixEnd_3100085 := by exact prefixLift 3100085
  have htrace : WordTrace (prefixWord ++ tailWord_3100085) baseStart_3100085 baseEnd_3100085 := by
    simpa [prefixWord, tailWord_3100085, baseEnd_3100085] using wordTrace_append hprefix tailTrace_3100085
  have hstable : (prefixWord ++ tailWord_3100085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100085).length < 2 ^ (prefixWord ++ tailWord_3100085).sum := by decide
  have hdescent : baseEnd_3100085 < baseStart_3100085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100111 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 3, 3, 2]
def baseStart_3100111 : Nat := 118140960795 + 3100111 * 2 ^ 59
def prefixEnd_3100111 : Nat := 4983230072969 + 3 ^ 40 * 3100111 * 2
def baseEnd_3100111 : Nat := 1591847025290625535155355

theorem tailTrace_3100111 : CollatzResearch.WordTrace tailWord_3100111 prefixEnd_3100111 1591847025290625535155355 := by
  unfold tailWord_3100111
  simp only [CollatzResearch.WordTrace]
  refine ⟨113070337271834778651700187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75380224847889852434466791 113070337271834778651700187)
  ·
    refine ⟨169605505907752167977550281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113070337271834778651700187 169605505907752167977550281)
    ·
      refine ⟨127204129430814125983162711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169605505907752167977550281 127204129430814125983162711)
      ·
        refine ⟨190806194146221188974744067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127204129430814125983162711 190806194146221188974744067)
        ·
          refine ⟨286209291219331783462116101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190806194146221188974744067 286209291219331783462116101)
          ·
            refine ⟨53664242103624709399146769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286209291219331783462116101 53664242103624709399146769)
            ·
              refine ⟨40248181577718532049360077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53664242103624709399146769 40248181577718532049360077)
              ·
                refine ⟨15093068091644449518510029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40248181577718532049360077 15093068091644449518510029)
                ·
                  refine ⟨5659900534366668569441261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15093068091644449518510029 5659900534366668569441261)
                  ·
                    refine ⟨2122462700387500713540473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5659900534366668569441261 2122462700387500713540473)
                    ·
                      refine ⟨1591847025290625535155355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122462700387500713540473 1591847025290625535155355)
                      ·
                        rfl

theorem cell23_3100111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3, 2].length) (baseStart_3100111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100111 prefixEnd_3100111 := by exact prefixLift 3100111
  have htrace : WordTrace (prefixWord ++ tailWord_3100111) baseStart_3100111 baseEnd_3100111 := by
    simpa [prefixWord, tailWord_3100111, baseEnd_3100111] using wordTrace_append hprefix tailTrace_3100111
  have hstable : (prefixWord ++ tailWord_3100111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100111).length < 2 ^ (prefixWord ++ tailWord_3100111).sum := by decide
  have hdescent : baseEnd_3100111 < baseStart_3100111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100154 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_3100154 : Nat := 118140960795 + 3100154 * 2 ^ 59
def prefixEnd_3100154 : Nat := 4983230072969 + 3 ^ 40 * 3100154 * 2
def baseEnd_3100154 : Nat := 1591869104958768866917657

theorem tailTrace_3100154 : CollatzResearch.WordTrace tailWord_3100154 prefixEnd_3100154 1591869104958768866917657 := by
  unfold tailWord_3100154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267976402669749248878879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75381270407119331330343677 28267976402669749248878879)
  ·
    refine ⟨42401964604004623873318319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28267976402669749248878879 42401964604004623873318319)
    ·
      refine ⟨63602946906006935809977479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42401964604004623873318319 63602946906006935809977479)
      ·
        refine ⟨95404420359010403714966219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63602946906006935809977479 95404420359010403714966219)
        ·
          refine ⟨143106630538515605572449329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95404420359010403714966219 143106630538515605572449329)
          ·
            refine ⟨107329972903886704179336997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143106630538515605572449329 107329972903886704179336997)
            ·
              refine ⟨20124369919478757033625687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107329972903886704179336997 20124369919478757033625687)
              ·
                refine ⟨30186554879218135550438531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20124369919478757033625687 30186554879218135550438531)
                ·
                  refine ⟨45279832318827203325657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30186554879218135550438531 45279832318827203325657797)
                  ·
                    refine ⟨8489968559780100623560837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45279832318827203325657797 8489968559780100623560837)
                    ·
                      refine ⟨1591869104958768866917657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8489968559780100623560837 1591869104958768866917657)
                      ·
                        rfl

theorem cell23_3100154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_3100154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100154 prefixEnd_3100154 := by exact prefixLift 3100154
  have htrace : WordTrace (prefixWord ++ tailWord_3100154) baseStart_3100154 baseEnd_3100154 := by
    simpa [prefixWord, tailWord_3100154, baseEnd_3100154] using wordTrace_append hprefix tailTrace_3100154
  have hstable : (prefixWord ++ tailWord_3100154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100154).length < 2 ^ (prefixWord ++ tailWord_3100154).sum := by decide
  have hdescent : baseEnd_3100154 < baseStart_3100154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100162 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3100162 : Nat := 118140960795 + 3100162 * 2 ^ 59
def prefixEnd_3100162 : Nat := 4983230072969 + 3 ^ 40 * 3100162 * 2
def baseEnd_3100162 : Nat := 1591873212804004835617621

theorem tailTrace_3100162 : CollatzResearch.WordTrace tailWord_3100162 prefixEnd_3100162 1591873212804004835617621 := by
  unfold tailWord_3100162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28268049348662503590451685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75381464929766676241204493 28268049348662503590451685)
  ·
    refine ⟨5300259252874219423209691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28268049348662503590451685 5300259252874219423209691)
    ·
      refine ⟨7950388879311329134814537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300259252874219423209691 7950388879311329134814537)
      ·
        refine ⟨5962791659483496851110903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7950388879311329134814537 5962791659483496851110903)
        ·
          refine ⟨8944187489225245276666355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5962791659483496851110903 8944187489225245276666355)
          ·
            refine ⟨13416281233837867914999533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944187489225245276666355 13416281233837867914999533)
            ·
              refine ⟨5031105462689200468124825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13416281233837867914999533 5031105462689200468124825)
              ·
                refine ⟨3773329097016900351093619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031105462689200468124825 3773329097016900351093619)
                ·
                  refine ⟨5659993645525350526640429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773329097016900351093619 5659993645525350526640429)
                  ·
                    refine ⟨2122497617072006447490161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5659993645525350526640429 2122497617072006447490161)
                    ·
                      refine ⟨1591873212804004835617621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122497617072006447490161 1591873212804004835617621)
                      ·
                        rfl

theorem cell23_3100162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3100162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100162 prefixEnd_3100162 := by exact prefixLift 3100162
  have htrace : WordTrace (prefixWord ++ tailWord_3100162) baseStart_3100162 baseEnd_3100162 := by
    simpa [prefixWord, tailWord_3100162, baseEnd_3100162] using wordTrace_append hprefix tailTrace_3100162
  have hstable : (prefixWord ++ tailWord_3100162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100162).length < 2 ^ (prefixWord ++ tailWord_3100162).sum := by decide
  have hdescent : baseEnd_3100162 < baseStart_3100162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100192 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3100192 : Nat := 118140960795 + 3100192 * 2 ^ 59
def prefixEnd_3100192 : Nat := 4983230072969 + 3 ^ 40 * 3100192 * 2
def baseEnd_3100192 : Nat := 1591888617223639718242483

theorem tailTrace_3100192 : CollatzResearch.WordTrace tailWord_3100192 prefixEnd_3100192 1591888617223639718242483 := by
  unfold tailWord_3100192
  simp only [CollatzResearch.WordTrace]
  refine ⟨56536645792270664742699415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75382194389694219656932553 56536645792270664742699415)
  ·
    refine ⟨84804968688405997114049123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56536645792270664742699415 84804968688405997114049123)
    ·
      refine ⟨127207453032608995671073685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84804968688405997114049123 127207453032608995671073685)
      ·
        refine ⟨5962849360903546672081579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127207453032608995671073685 5962849360903546672081579)
        ·
          refine ⟨8944274041355320008122369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5962849360903546672081579 8944274041355320008122369)
          ·
            refine ⟨6708205531016490006091777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8944274041355320008122369 6708205531016490006091777)
            ·
              refine ⟨5031154148262367504568833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708205531016490006091777 5031154148262367504568833)
              ·
                refine ⟨3773365611196775628426625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031154148262367504568833 3773365611196775628426625)
                ·
                  refine ⟨2830024208397581721319969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3773365611196775628426625 2830024208397581721319969)
                  ·
                    refine ⟨2122518156298186290989977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2830024208397581721319969 2122518156298186290989977)
                    ·
                      refine ⟨1591888617223639718242483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122518156298186290989977 1591888617223639718242483)
                      ·
                        rfl

theorem cell23_3100192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3100192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100192 prefixEnd_3100192 := by exact prefixLift 3100192
  have htrace : WordTrace (prefixWord ++ tailWord_3100192) baseStart_3100192 baseEnd_3100192 := by
    simpa [prefixWord, tailWord_3100192, baseEnd_3100192] using wordTrace_append hprefix tailTrace_3100192
  have hstable : (prefixWord ++ tailWord_3100192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100192).length < 2 ^ (prefixWord ++ tailWord_3100192).sum := by decide
  have hdescent : baseEnd_3100192 < baseStart_3100192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100241 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 5, 4]
def baseStart_3100241 : Nat := 118140960795 + 3100241 * 2 ^ 59
def prefixEnd_3100241 : Nat := 4983230072969 + 3 ^ 40 * 3100241 * 2
def baseEnd_3100241 : Nat := 530637925925236675509919

theorem tailTrace_3100241 : CollatzResearch.WordTrace tailWord_3100241 prefixEnd_3100241 530637925925236675509919 := by
  unfold tailWord_3100241
  simp only [CollatzResearch.WordTrace]
  refine ⟨113075078761363810853932577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75383385840909207235955051 113075078761363810853932577)
  ·
    refine ⟨84806309071022858140449433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113075078761363810853932577 84806309071022858140449433)
    ·
      refine ⟨63604731803267143605337075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84806309071022858140449433 63604731803267143605337075)
      ·
        refine ⟨95407097704900715408005613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63604731803267143605337075 95407097704900715408005613)
        ·
          refine ⟨35777661639337768278002105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95407097704900715408005613 35777661639337768278002105)
          ·
            refine ⟨26833246229503326208501579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35777661639337768278002105 26833246229503326208501579)
            ·
              refine ⟨40249869344254989312752369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26833246229503326208501579 40249869344254989312752369)
              ·
                refine ⟨30187402008191241984564277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40249869344254989312752369 30187402008191241984564277)
                ·
                  refine ⟨2830068938267928936052901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30187402008191241984564277 2830068938267928936052901)
                  ·
                    refine ⟨530637925925236675509919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830068938267928936052901 530637925925236675509919)
                    ·
                      rfl

theorem cell23_3100241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_3100241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100241 prefixEnd_3100241 := by exact prefixLift 3100241
  have htrace : WordTrace (prefixWord ++ tailWord_3100241) baseStart_3100241 baseEnd_3100241 := by
    simpa [prefixWord, tailWord_3100241, baseEnd_3100241] using wordTrace_append hprefix tailTrace_3100241
  have hstable : (prefixWord ++ tailWord_3100241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100241).length < 2 ^ (prefixWord ++ tailWord_3100241).sum := by decide
  have hdescent : baseEnd_3100241 < baseStart_3100241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100281 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_3100281 : Nat := 118140960795 + 3100281 * 2 ^ 59
def prefixEnd_3100281 : Nat := 4983230072969 + 3 ^ 40 * 3100281 * 2
def baseEnd_3100281 : Nat := 1591934317001889870029573

theorem tailTrace_3100281 : CollatzResearch.WordTrace tailWord_3100281 prefixEnd_3100281 1591934317001889870029573 := by
  unfold tailWord_3100281
  simp only [CollatzResearch.WordTrace]
  refine ⟨113076537681218897685388697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75384358454145931790259131 113076537681218897685388697)
  ·
    refine ⟨84807403260914173264041523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113076537681218897685388697 84807403260914173264041523)
    ·
      refine ⟨127211104891371259896062285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84807403260914173264041523 127211104891371259896062285)
      ·
        refine ⟨47704164334264222461023357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127211104891371259896062285 47704164334264222461023357)
        ·
          refine ⟨17889061625349083422883759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47704164334264222461023357 17889061625349083422883759)
          ·
            refine ⟨26833592438023625134325639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17889061625349083422883759 26833592438023625134325639)
            ·
              refine ⟨40250388657035437701488459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26833592438023625134325639 40250388657035437701488459)
              ·
                refine ⟨60375582985553156552232689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40250388657035437701488459 60375582985553156552232689)
                ·
                  refine ⟨45281687239164867414174517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60375582985553156552232689 45281687239164867414174517)
                  ·
                    refine ⟨4245158178671706320078861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45281687239164867414174517 4245158178671706320078861)
                    ·
                      refine ⟨1591934317001889870029573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245158178671706320078861 1591934317001889870029573)
                      ·
                        rfl

theorem cell23_3100281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_3100281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100281 prefixEnd_3100281 := by exact prefixLift 3100281
  have htrace : WordTrace (prefixWord ++ tailWord_3100281) baseStart_3100281 baseEnd_3100281 := by
    simpa [prefixWord, tailWord_3100281, baseEnd_3100281] using wordTrace_append hprefix tailTrace_3100281
  have hstable : (prefixWord ++ tailWord_3100281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100281).length < 2 ^ (prefixWord ++ tailWord_3100281).sum := by decide
  have hdescent : baseEnd_3100281 < baseStart_3100281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100338 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_3100338 : Nat := 118140960795 + 3100338 * 2 ^ 59
def prefixEnd_3100338 : Nat := 4983230072969 + 3 ^ 40 * 3100338 * 2
def baseEnd_3100338 : Nat := 1591963585399196147016811

theorem tailTrace_3100338 : CollatzResearch.WordTrace tailWord_3100338 prefixEnd_3100338 1591963585399196147016811 := by
  unfold tailWord_3100338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269654160503099105053417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75385744428008264280142445 28269654160503099105053417)
  ·
    refine ⟨21202240620377324328790063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28269654160503099105053417 21202240620377324328790063)
    ·
      refine ⟨31803360930565986493185095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21202240620377324328790063 31803360930565986493185095)
      ·
        refine ⟨47705041395848979739777643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31803360930565986493185095 47705041395848979739777643)
        ·
          refine ⟨71557562093773469609666465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47705041395848979739777643 71557562093773469609666465)
          ·
            refine ⟨53668171570330102207249849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71557562093773469609666465 53668171570330102207249849)
            ·
              refine ⟨40251128677747576655437387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53668171570330102207249849 40251128677747576655437387)
              ·
                refine ⟨60376693016621364983156081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40251128677747576655437387 60376693016621364983156081)
                ·
                  refine ⟨45282519762466023737367061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60376693016621364983156081 45282519762466023737367061)
                  ·
                    refine ⟨2122618113865594862689081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45282519762466023737367061 2122618113865594862689081)
                    ·
                      refine ⟨1591963585399196147016811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122618113865594862689081 1591963585399196147016811)
                      ·
                        rfl

theorem cell23_3100338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_3100338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100338 prefixEnd_3100338 := by exact prefixLift 3100338
  have htrace : WordTrace (prefixWord ++ tailWord_3100338) baseStart_3100338 baseEnd_3100338 := by
    simpa [prefixWord, tailWord_3100338, baseEnd_3100338] using wordTrace_append hprefix tailTrace_3100338
  have hstable : (prefixWord ++ tailWord_3100338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100338).length < 2 ^ (prefixWord ++ tailWord_3100338).sum := by decide
  have hdescent : baseEnd_3100338 < baseStart_3100338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100348 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_3100348 : Nat := 118140960795 + 3100348 * 2 ^ 59
def prefixEnd_3100348 : Nat := 4983230072969 + 3 ^ 40 * 3100348 * 2
def baseEnd_3100348 : Nat := 530656240068580369297255

theorem tailTrace_3100348 : CollatzResearch.WordTrace tailWord_3100348 prefixEnd_3100348 530656240068580369297255 := by
  unfold tailWord_3100348
  simp only [CollatzResearch.WordTrace]
  refine ⟨56539490685988084064038849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75385987581317445418718465 56539490685988084064038849)
  ·
    refine ⟨42404618014491063048029137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56539490685988084064038849 42404618014491063048029137)
    ·
      refine ⟨31803463510868297286021853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42404618014491063048029137 31803463510868297286021853)
      ·
        refine ⟨11926298816575611482258195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31803463510868297286021853 11926298816575611482258195)
        ·
          refine ⟨17889448224863417223387293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11926298816575611482258195 17889448224863417223387293)
          ·
            refine ⟨6708543084323781458770235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17889448224863417223387293 6708543084323781458770235)
            ·
              refine ⟨10062814626485672188155353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708543084323781458770235 10062814626485672188155353)
              ·
                refine ⟨7547110969864254141116515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10062814626485672188155353 7547110969864254141116515)
                ·
                  refine ⟨11320666454796381211674773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547110969864254141116515 11320666454796381211674773)
                  ·
                    refine ⟨530656240068580369297255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11320666454796381211674773 530656240068580369297255)
                    ·
                      rfl

theorem cell23_3100348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_3100348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100348 prefixEnd_3100348 := by exact prefixLift 3100348
  have htrace : WordTrace (prefixWord ++ tailWord_3100348) baseStart_3100348 baseEnd_3100348 := by
    simpa [prefixWord, tailWord_3100348, baseEnd_3100348] using wordTrace_append hprefix tailTrace_3100348
  have hstable : (prefixWord ++ tailWord_3100348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100348).length < 2 ^ (prefixWord ++ tailWord_3100348).sum := by decide
  have hdescent : baseEnd_3100348 < baseStart_3100348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100378 : List Nat := [3, 1, 1, 2, 2, 5, 1, 8]
def baseStart_3100378 : Nat := 118140960795 + 3100378 * 2 ^ 59
def prefixEnd_3100378 : Nat := 4983230072969 + 3 ^ 40 * 3100378 * 2
def baseEnd_3100378 : Nat := 58962374986125036685801

theorem tailTrace_3100378 : CollatzResearch.WordTrace tailWord_3100378 prefixEnd_3100378 58962374986125036685801 := by
  unfold tailWord_3100378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28270018890466870812917447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75386717041244988834446525 28270018890466870812917447)
  ·
    refine ⟨42405028335700306219376171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28270018890466870812917447 42405028335700306219376171)
    ·
      refine ⟨63607542503550459329064257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42405028335700306219376171 63607542503550459329064257)
      ·
        refine ⟨47705656877662844496798193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63607542503550459329064257 47705656877662844496798193)
        ·
          refine ⟨35779242658247133372598645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47705656877662844496798193 35779242658247133372598645)
          ·
            refine ⟨3354303999210668753681123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35779242658247133372598645 3354303999210668753681123)
            ·
              refine ⟨5031455998816003130521685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354303999210668753681123 5031455998816003130521685)
              ·
                refine ⟨58962374986125036685801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5031455998816003130521685 58962374986125036685801)
                ·
                  rfl

theorem cell23_3100378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_3100378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100378 prefixEnd_3100378 := by exact prefixLift 3100378
  have htrace : WordTrace (prefixWord ++ tailWord_3100378) baseStart_3100378 baseEnd_3100378 := by
    simpa [prefixWord, tailWord_3100378, baseEnd_3100378] using wordTrace_append hprefix tailTrace_3100378
  have hstable : (prefixWord ++ tailWord_3100378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100378).length < 2 ^ (prefixWord ++ tailWord_3100378).sum := by decide
  have hdescent : baseEnd_3100378 < baseStart_3100378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100385 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_3100385 : Nat := 118140960795 + 3100385 * 2 ^ 59
def prefixEnd_3100385 : Nat := 4983230072969 + 3 ^ 40 * 3100385 * 2
def baseEnd_3100385 : Nat := 1591987718989957463129095

theorem tailTrace_3100385 : CollatzResearch.WordTrace tailWord_3100385 prefixEnd_3100385 1591987718989957463129095 := by
  unfold tailWord_3100385
  simp only [CollatzResearch.WordTrace]
  refine ⟨113080330872842123447174609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75386887248561415631449739 113080330872842123447174609)
  ·
    refine ⟨84810248154631592585380957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113080330872842123447174609 84810248154631592585380957)
    ·
      refine ⟨31803843057986847219517859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84810248154631592585380957 31803843057986847219517859)
      ·
        refine ⟨47705764586980270829276789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31803843057986847219517859 47705764586980270829276789)
        ·
          refine ⟨4472415430029400390244699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47705764586980270829276789 4472415430029400390244699)
          ·
            refine ⟨6708623145044100585367049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472415430029400390244699 6708623145044100585367049)
            ·
              refine ⟨5031467358783075439025287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708623145044100585367049 5031467358783075439025287)
              ·
                refine ⟨7547201038174613158537931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031467358783075439025287 7547201038174613158537931)
                ·
                  refine ⟨11320801557261919737806897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547201038174613158537931 11320801557261919737806897)
                  ·
                    refine ⟨8490601167946439803355173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11320801557261919737806897 8490601167946439803355173)
                    ·
                      refine ⟨1591987718989957463129095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8490601167946439803355173 1591987718989957463129095)
                      ·
                        rfl

theorem cell23_3100385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_3100385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100385 prefixEnd_3100385 := by exact prefixLift 3100385
  have htrace : WordTrace (prefixWord ++ tailWord_3100385) baseStart_3100385 baseEnd_3100385 := by
    simpa [prefixWord, tailWord_3100385, baseEnd_3100385] using wordTrace_append hprefix tailTrace_3100385
  have hstable : (prefixWord ++ tailWord_3100385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100385).length < 2 ^ (prefixWord ++ tailWord_3100385).sum := by decide
  have hdescent : baseEnd_3100385 < baseStart_3100385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100406 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_3100406 : Nat := 118140960795 + 3100406 * 2 ^ 59
def prefixEnd_3100406 : Nat := 4983230072969 + 3 ^ 40 * 3100406 * 2
def baseEnd_3100406 : Nat := 1591998502083701880966499

theorem tailTrace_3100406 : CollatzResearch.WordTrace tailWord_3100406 prefixEnd_3100406 1591998502083701880966499 := by
  unfold tailWord_3100406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067568550360377752105567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75387397870510696022459381 7067568550360377752105567)
  ·
    refine ⟨10601352825540566628158351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7067568550360377752105567 10601352825540566628158351)
    ·
      refine ⟨15902029238310849942237527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10601352825540566628158351 15902029238310849942237527)
      ·
        refine ⟨23853043857466274913356291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15902029238310849942237527 23853043857466274913356291)
        ·
          refine ⟨35779565786199412370034437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23853043857466274913356291 35779565786199412370034437)
          ·
            refine ⟨6708668584912389819381457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35779565786199412370034437 6708668584912389819381457)
            ·
              refine ⟨5031501438684292364536093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708668584912389819381457 5031501438684292364536093)
              ·
                refine ⟨1886813039506609636701035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5031501438684292364536093 1886813039506609636701035)
                ·
                  refine ⟨2830219559259914455051553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886813039506609636701035 2830219559259914455051553)
                  ·
                    refine ⟨2122664669444935841288665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2830219559259914455051553 2122664669444935841288665)
                    ·
                      refine ⟨1591998502083701880966499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122664669444935841288665 1591998502083701880966499)
                      ·
                        rfl

theorem cell23_3100406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_3100406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100406 prefixEnd_3100406 := by exact prefixLift 3100406
  have htrace : WordTrace (prefixWord ++ tailWord_3100406) baseStart_3100406 baseEnd_3100406 := by
    simpa [prefixWord, tailWord_3100406, baseEnd_3100406] using wordTrace_append hprefix tailTrace_3100406
  have hstable : (prefixWord ++ tailWord_3100406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100406).length < 2 ^ (prefixWord ++ tailWord_3100406).sum := by decide
  have hdescent : baseEnd_3100406 < baseStart_3100406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100411 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4]
def baseStart_3100411 : Nat := 118140960795 + 3100411 * 2 ^ 59
def prefixEnd_3100411 : Nat := 4983230072969 + 3 ^ 40 * 3100411 * 2
def baseEnd_3100411 : Nat := 1592001069486974361403975

theorem tailTrace_3100411 : CollatzResearch.WordTrace tailWord_3100411 prefixEnd_3100411 1592001069486974361403975 := by
  unfold tailWord_3100411
  simp only [CollatzResearch.WordTrace]
  refine ⟨113081279170747929887621087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75387519447165286591747391 113081279170747929887621087)
  ·
    refine ⟨169621918756121894831431631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113081279170747929887621087 169621918756121894831431631)
    ·
      refine ⟨254432878134182842247147447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169621918756121894831431631 254432878134182842247147447)
      ·
        refine ⟨381649317201274263370721171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254432878134182842247147447 381649317201274263370721171)
        ·
          refine ⟨572473975801911395056081757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381649317201274263370721171 572473975801911395056081757)
          ·
            refine ⟨214677740925716773146030659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572473975801911395056081757 214677740925716773146030659)
            ·
              refine ⟨322016611388575159719045989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214677740925716773146030659 322016611388575159719045989)
              ·
                refine ⟨60378114635357842447321123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322016611388575159719045989 60378114635357842447321123)
                ·
                  refine ⟨90567171953036763670981685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60378114635357842447321123 90567171953036763670981685)
                  ·
                    refine ⟨8490672370597196594154533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90567171953036763670981685 8490672370597196594154533)
                    ·
                      refine ⟨1592001069486974361403975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8490672370597196594154533 1592001069486974361403975)
                      ·
                        rfl

theorem cell23_3100411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_3100411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100411 prefixEnd_3100411 := by exact prefixLift 3100411
  have htrace : WordTrace (prefixWord ++ tailWord_3100411) baseStart_3100411 baseEnd_3100411 := by
    simpa [prefixWord, tailWord_3100411, baseEnd_3100411] using wordTrace_append hprefix tailTrace_3100411
  have hstable : (prefixWord ++ tailWord_3100411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100411).length < 2 ^ (prefixWord ++ tailWord_3100411).sum := by decide
  have hdescent : baseEnd_3100411 < baseStart_3100411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100431 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_3100431 : Nat := 118140960795 + 3100431 * 2 ^ 59
def prefixEnd_3100431 : Nat := 4983230072969 + 3 ^ 40 * 3100431 * 2
def baseEnd_3100431 : Nat := 1592011339100064283153883

theorem tailTrace_3100431 : CollatzResearch.WordTrace tailWord_3100431 prefixEnd_3100431 1592011339100064283153883 := by
  unfold tailWord_3100431
  simp only [CollatzResearch.WordTrace]
  refine ⟨113082008630675473303349147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75388005753783648868899431 113082008630675473303349147)
  ·
    refine ⟨169623012946013209955023721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113082008630675473303349147 169623012946013209955023721)
    ·
      refine ⟨127217259709509907466267791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169623012946013209955023721 127217259709509907466267791)
      ·
        refine ⟨190825889564264861199401687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127217259709509907466267791 190825889564264861199401687)
        ·
          refine ⟨286238834346397291799102531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190825889564264861199401687 286238834346397291799102531)
          ·
            refine ⟨429358251519595937698653797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286238834346397291799102531 429358251519595937698653797)
            ·
              refine ⟨80504672159924238318497587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 429358251519595937698653797 80504672159924238318497587)
              ·
                refine ⟨120757008239886357477746381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80504672159924238318497587 120757008239886357477746381)
                ·
                  refine ⟨45283878089957384054154893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120757008239886357477746381 45283878089957384054154893)
                  ·
                    refine ⟨16981454283734019020308085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45283878089957384054154893 16981454283734019020308085)
                    ·
                      refine ⟨1592011339100064283153883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16981454283734019020308085 1592011339100064283153883)
                      ·
                        rfl

theorem cell23_3100431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_3100431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100431 prefixEnd_3100431 := by exact prefixLift 3100431
  have htrace : WordTrace (prefixWord ++ tailWord_3100431) baseStart_3100431 baseEnd_3100431 := by
    simpa [prefixWord, tailWord_3100431, baseEnd_3100431] using wordTrace_append hprefix tailTrace_3100431
  have hstable : (prefixWord ++ tailWord_3100431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100431).length < 2 ^ (prefixWord ++ tailWord_3100431).sum := by decide
  have hdescent : baseEnd_3100431 < baseStart_3100431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100436 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3100436 : Nat := 118140960795 + 3100436 * 2 ^ 59
def prefixEnd_3100436 : Nat := 4983230072969 + 3 ^ 40 * 3100436 * 2
def baseEnd_3100436 : Nat := 1592013906503336763591361

theorem tailTrace_3100436 : CollatzResearch.WordTrace tailWord_3100436 prefixEnd_3100436 1592013906503336763591361 := by
  unfold tailWord_3100436
  simp only [CollatzResearch.WordTrace]
  refine ⟨56541095497828679578640581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75388127330438239438187441 56541095497828679578640581)
  ·
    refine ⟨10601455405842877420995109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56541095497828679578640581 10601455405842877420995109)
    ·
      refine ⟨1987772888595539516436583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10601455405842877420995109 1987772888595539516436583)
      ·
        refine ⟨2981659332893309274654875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987772888595539516436583 2981659332893309274654875)
        ·
          refine ⟨4472488999339963911982313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981659332893309274654875 4472488999339963911982313)
          ·
            refine ⟨3354366749504972933986735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4472488999339963911982313 3354366749504972933986735)
            ·
              refine ⟨5031550124257459400980103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354366749504972933986735 5031550124257459400980103)
              ·
                refine ⟨7547325186386189101470155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031550124257459400980103 7547325186386189101470155)
                ·
                  refine ⟨11320987779579283652205233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547325186386189101470155 11320987779579283652205233)
                  ·
                    refine ⟨8490740834684462739153925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11320987779579283652205233 8490740834684462739153925)
                    ·
                      refine ⟨1592013906503336763591361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8490740834684462739153925 1592013906503336763591361)
                      ·
                        rfl

theorem cell23_3100436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3100436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100436 prefixEnd_3100436 := by exact prefixLift 3100436
  have htrace : WordTrace (prefixWord ++ tailWord_3100436) baseStart_3100436 baseEnd_3100436 := by
    simpa [prefixWord, tailWord_3100436, baseEnd_3100436] using wordTrace_append hprefix tailTrace_3100436
  have hstable : (prefixWord ++ tailWord_3100436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100436).length < 2 ^ (prefixWord ++ tailWord_3100436).sum := by decide
  have hdescent : baseEnd_3100436 < baseStart_3100436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100439 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 2, 1, 3]
def baseStart_3100439 : Nat := 118140960795 + 3100439 * 2 ^ 59
def prefixEnd_3100439 : Nat := 4983230072969 + 3 ^ 40 * 3100439 * 2
def baseEnd_3100439 : Nat := 1592015446945300251853847

theorem tailTrace_3100439 : CollatzResearch.WordTrace tailWord_3100439 prefixEnd_3100439 1592015446945300251853847 := by
  unfold tailWord_3100439
  simp only [CollatzResearch.WordTrace]
  refine ⟨113082300414646490669640371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75388200276430993779760247 113082300414646490669640371)
  ·
    refine ⟨169623450621969736004460557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113082300414646490669640371 169623450621969736004460557)
    ·
      refine ⟨63608793983238651001672709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169623450621969736004460557 63608793983238651001672709)
      ·
        refine ⟨11926648871857247062813633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63608793983238651001672709 11926648871857247062813633)
        ·
          refine ⟨8944986653892935297110225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11926648871857247062813633 8944986653892935297110225)
          ·
            refine ⟨6708739990419701472832669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8944986653892935297110225 6708739990419701472832669)
            ·
              refine ⟨2515777496407388052312251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6708739990419701472832669 2515777496407388052312251)
              ·
                refine ⟨3773666244611082078468377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515777496407388052312251 3773666244611082078468377)
                ·
                  refine ⟨2830249683458311558851283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3773666244611082078468377 2830249683458311558851283)
                  ·
                    refine ⟨4245374525187467338276925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830249683458311558851283 4245374525187467338276925)
                    ·
                      refine ⟨1592015446945300251853847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245374525187467338276925 1592015446945300251853847)
                      ·
                        rfl

theorem cell23_3100439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_3100439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100439 prefixEnd_3100439 := by exact prefixLift 3100439
  have htrace : WordTrace (prefixWord ++ tailWord_3100439) baseStart_3100439 baseEnd_3100439 := by
    simpa [prefixWord, tailWord_3100439, baseEnd_3100439] using wordTrace_append hprefix tailTrace_3100439
  have hstable : (prefixWord ++ tailWord_3100439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100439).length < 2 ^ (prefixWord ++ tailWord_3100439).sum := by decide
  have hdescent : baseEnd_3100439 < baseStart_3100439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100446 : List Nat := [4, 3, 2, 2, 2, 1, 2, 7]
def baseStart_3100446 : Nat := 118140960795 + 3100446 * 2 ^ 59
def prefixEnd_3100446 : Nat := 4983230072969 + 3 ^ 40 * 3100446 * 2
def baseEnd_3100446 : Nat := 58963668196662286091345

theorem tailTrace_3100446 : CollatzResearch.WordTrace tailWord_3100446 prefixEnd_3100446 58963668196662286091345 := by
  unfold tailWord_3100446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14135319465702641358143149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75388370483747420576763461 14135319465702641358143149)
  ·
    refine ⟨5300744799638490509303681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14135319465702641358143149 5300744799638490509303681)
    ·
      refine ⟨3975558599728867881977761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5300744799638490509303681 3975558599728867881977761)
      ·
        refine ⟨2981668949796650911483321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3975558599728867881977761 2981668949796650911483321)
        ·
          refine ⟨2236251712347488183612491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981668949796650911483321 2236251712347488183612491)
          ·
            refine ⟨3354377568521232275418737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236251712347488183612491 3354377568521232275418737)
            ·
              refine ⟨2515783176390924206564053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3354377568521232275418737 2515783176390924206564053)
              ·
                refine ⟨58963668196662286091345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2515783176390924206564053 58963668196662286091345)
                ·
                  rfl

theorem cell23_3100446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_3100446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100446 prefixEnd_3100446 := by exact prefixLift 3100446
  have htrace : WordTrace (prefixWord ++ tailWord_3100446) baseStart_3100446 baseEnd_3100446 := by
    simpa [prefixWord, tailWord_3100446, baseEnd_3100446] using wordTrace_append hprefix tailTrace_3100446
  have hstable : (prefixWord ++ tailWord_3100446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100446).length < 2 ^ (prefixWord ++ tailWord_3100446).sum := by decide
  have hdescent : baseEnd_3100446 < baseStart_3100446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100448 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3100448 : Nat := 118140960795 + 3100448 * 2 ^ 59
def prefixEnd_3100448 : Nat := 4983230072969 + 3 ^ 40 * 3100448 * 2
def baseEnd_3100448 : Nat := 1592020068271190716641305

theorem tailTrace_3100448 : CollatzResearch.WordTrace tailWord_3100448 prefixEnd_3100448 1592020068271190716641305 := by
  unfold tailWord_3100448
  simp only [CollatzResearch.WordTrace]
  refine ⟨56541314335806942603358999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75388419114409256804478665 56541314335806942603358999)
  ·
    refine ⟨84811971503710413905038499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56541314335806942603358999 84811971503710413905038499)
    ·
      refine ⟨127217957255565620857557749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84811971503710413905038499 127217957255565620857557749)
      ·
        refine ⟨11926683492709276955396039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127217957255565620857557749 11926683492709276955396039)
        ·
          refine ⟨17890025239063915433094059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11926683492709276955396039 17890025239063915433094059)
          ·
            refine ⟨26835037858595873149641089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17890025239063915433094059 26835037858595873149641089)
            ·
              refine ⟨20126278393946904862230817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26835037858595873149641089 20126278393946904862230817)
              ·
                refine ⟨15094708795460178646673113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20126278393946904862230817 15094708795460178646673113)
                ·
                  refine ⟨11321031596595133985004835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15094708795460178646673113 11321031596595133985004835)
                  ·
                    refine ⟨16981547394892700977507253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11321031596595133985004835 16981547394892700977507253)
                    ·
                      refine ⟨1592020068271190716641305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16981547394892700977507253 1592020068271190716641305)
                      ·
                        rfl

theorem cell23_3100448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3100448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100448 prefixEnd_3100448 := by exact prefixLift 3100448
  have htrace : WordTrace (prefixWord ++ tailWord_3100448) baseStart_3100448 baseEnd_3100448 := by
    simpa [prefixWord, tailWord_3100448, baseEnd_3100448] using wordTrace_append hprefix tailTrace_3100448
  have hstable : (prefixWord ++ tailWord_3100448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100448).length < 2 ^ (prefixWord ++ tailWord_3100448).sum := by decide
  have hdescent : baseEnd_3100448 < baseStart_3100448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100542 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3100542 : Nat := 118140960795 + 3100542 * 2 ^ 59
def prefixEnd_3100542 : Nat := 4983230072969 + 3 ^ 40 * 3100542 * 2
def baseEnd_3100542 : Nat := 1592068335452713348865873

theorem tailTrace_3100542 : CollatzResearch.WordTrace tailWord_3100542 prefixEnd_3100542 1592068335452713348865873 := by
  unfold tailWord_3100542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14135757141659167407579985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75390704755515559507093253 14135757141659167407579985)
  ·
    refine ⟨10601817856244375555684989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14135757141659167407579985 10601817856244375555684989)
    ·
      refine ⟨3975681696091640833381871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10601817856244375555684989 3975681696091640833381871)
      ·
        refine ⟨5963522544137461250072807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975681696091640833381871 5963522544137461250072807)
        ·
          refine ⟨8945283816206191875109211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5963522544137461250072807 8945283816206191875109211)
          ·
            refine ⟨13417925724309287812663817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8945283816206191875109211 13417925724309287812663817)
            ·
              refine ⟨10063444293231965859497863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13417925724309287812663817 10063444293231965859497863)
              ·
                refine ⟨15095166439847948789246795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063444293231965859497863 15095166439847948789246795)
                ·
                  refine ⟨22642749659771923183870193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15095166439847948789246795 22642749659771923183870193)
                  ·
                    refine ⟨16982062244828942387902645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22642749659771923183870193 16982062244828942387902645)
                    ·
                      refine ⟨1592068335452713348865873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16982062244828942387902645 1592068335452713348865873)
                      ·
                        rfl

theorem cell23_3100542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3100542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100542 prefixEnd_3100542 := by exact prefixLift 3100542
  have htrace : WordTrace (prefixWord ++ tailWord_3100542) baseStart_3100542 baseEnd_3100542 := by
    simpa [prefixWord, tailWord_3100542, baseEnd_3100542] using wordTrace_append hprefix tailTrace_3100542
  have hstable : (prefixWord ++ tailWord_3100542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100542).length < 2 ^ (prefixWord ++ tailWord_3100542).sum := by decide
  have hdescent : baseEnd_3100542 < baseStart_3100542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100562 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3100562 : Nat := 118140960795 + 3100562 * 2 ^ 59
def prefixEnd_3100562 : Nat := 4983230072969 + 3 ^ 40 * 3100562 * 2
def baseEnd_3100562 : Nat := 530692868355267756871927

theorem tailTrace_3100562 : CollatzResearch.WordTrace tailWord_3100562 prefixEnd_3100562 530692868355267756871927 := by
  unfold tailWord_3100562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28271696648300220669091985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75391191062133921784245293 28271696648300220669091985)
  ·
    refine ⟨21203772486225165501818989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28271696648300220669091985 21203772486225165501818989)
    ·
      refine ⟨7951414682334437063182121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21203772486225165501818989 7951414682334437063182121)
      ·
        refine ⟨5963561011750827797386591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7951414682334437063182121 5963561011750827797386591)
        ·
          refine ⟨8945341517626241696079887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5963561011750827797386591 8945341517626241696079887)
          ·
            refine ⟨13418012276439362544119831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8945341517626241696079887 13418012276439362544119831)
            ·
              refine ⟨20127018414659043816179747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13418012276439362544119831 20127018414659043816179747)
              ·
                refine ⟨30190527621988565724269621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20127018414659043816179747 30190527621988565724269621)
                ·
                  refine ⟨2830361964561428036650277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30190527621988565724269621 2830361964561428036650277)
                  ·
                    refine ⟨530692868355267756871927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830361964561428036650277 530692868355267756871927)
                    ·
                      rfl

theorem cell23_3100562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3100562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100562 prefixEnd_3100562 := by exact prefixLift 3100562
  have htrace : WordTrace (prefixWord ++ tailWord_3100562) baseStart_3100562 baseEnd_3100562 := by
    simpa [prefixWord, tailWord_3100562, baseEnd_3100562] using wordTrace_append hprefix tailTrace_3100562
  have hstable : (prefixWord ++ tailWord_3100562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100562).length < 2 ^ (prefixWord ++ tailWord_3100562).sum := by decide
  have hdescent : baseEnd_3100562 < baseStart_3100562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100572 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3100572 : Nat := 118140960795 + 3100572 * 2 ^ 59
def prefixEnd_3100572 : Nat := 4983230072969 + 3 ^ 40 * 3100572 * 2
def baseEnd_3100572 : Nat := 1592083739872348231490735

theorem tailTrace_3100572 : CollatzResearch.WordTrace tailWord_3100572 prefixEnd_3100572 1592083739872348231490735 := by
  unfold tailWord_3100572
  simp only [CollatzResearch.WordTrace]
  refine ⟨56543575661582327192115985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75391434215443102922821313 56543575661582327192115985)
  ·
    refine ⟨42407681746186745394086989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56543575661582327192115985 42407681746186745394086989)
    ·
      refine ⟨15902880654820029522782621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42407681746186745394086989 15902880654820029522782621)
      ·
        refine ⟨5963580245557511071043483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15902880654820029522782621 5963580245557511071043483)
        ·
          refine ⟨8945370368336266606565225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5963580245557511071043483 8945370368336266606565225)
          ·
            refine ⟨6709027776252199954923919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8945370368336266606565225 6709027776252199954923919)
            ·
              refine ⟨10063541664378299932385879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6709027776252199954923919 10063541664378299932385879)
              ·
                refine ⟨15095312496567449898578819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063541664378299932385879 15095312496567449898578819)
                ·
                  refine ⟨22642968744851174847868229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15095312496567449898578819 22642968744851174847868229)
                  ·
                    refine ⟨4245556639659595283975293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22642968744851174847868229 4245556639659595283975293)
                    ·
                      refine ⟨1592083739872348231490735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245556639659595283975293 1592083739872348231490735)
                      ·
                        rfl

theorem cell23_3100572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3100572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100572 prefixEnd_3100572 := by exact prefixLift 3100572
  have htrace : WordTrace (prefixWord ++ tailWord_3100572) baseStart_3100572 baseEnd_3100572 := by
    simpa [prefixWord, tailWord_3100572, baseEnd_3100572] using wordTrace_append hprefix tailTrace_3100572
  have hstable : (prefixWord ++ tailWord_3100572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100572).length < 2 ^ (prefixWord ++ tailWord_3100572).sum := by decide
  have hdescent : baseEnd_3100572 < baseStart_3100572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100596 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3100596 : Nat := 118140960795 + 3100596 * 2 ^ 59
def prefixEnd_3100596 : Nat := 4983230072969 + 3 ^ 40 * 3100596 * 2
def baseEnd_3100596 : Nat := 530698687802685379196875

theorem tailTrace_3100596 : CollatzResearch.WordTrace tailWord_3100596 prefixEnd_3100596 530698687802685379196875 := by
  unfold tailWord_3100596
  simp only [CollatzResearch.WordTrace]
  refine ⟨56544013337538853241552821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75392017783385137655403761 56544013337538853241552821)
  ·
    refine ⟨5301001250394267491395577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56544013337538853241552821 5301001250394267491395577)
    ·
      refine ⟨3975750937795700618546683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5301001250394267491395577 3975750937795700618546683)
      ·
        refine ⟨5963626406693550927820025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975750937795700618546683 5963626406693550927820025)
        ·
          refine ⟨4472719805020163195865019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5963626406693550927820025 4472719805020163195865019)
          ·
            refine ⟨6709079707530244793797529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472719805020163195865019 6709079707530244793797529)
            ·
              refine ⟨5031809780647683595348147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6709079707530244793797529 5031809780647683595348147)
              ·
                refine ⟨7547714670971525393022221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031809780647683595348147 7547714670971525393022221)
                ·
                  refine ⟨2830393001614322022383333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7547714670971525393022221 2830393001614322022383333)
                  ·
                    refine ⟨530698687802685379196875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830393001614322022383333 530698687802685379196875)
                    ·
                      rfl

theorem cell23_3100596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3100596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100596 prefixEnd_3100596 := by exact prefixLift 3100596
  have htrace : WordTrace (prefixWord ++ tailWord_3100596) baseStart_3100596 baseEnd_3100596 := by
    simpa [prefixWord, tailWord_3100596, baseEnd_3100596] using wordTrace_append hprefix tailTrace_3100596
  have hstable : (prefixWord ++ tailWord_3100596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100596).length < 2 ^ (prefixWord ++ tailWord_3100596).sum := by decide
  have hdescent : baseEnd_3100596 < baseStart_3100596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100622 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_3100622 : Nat := 118140960795 + 3100622 * 2 ^ 59
def prefixEnd_3100622 : Nat := 4983230072969 + 3 ^ 40 * 3100622 * 2
def baseEnd_3100622 : Nat := 530703137968357678621835

theorem tailTrace_3100622 : CollatzResearch.WordTrace tailWord_3100622 prefixEnd_3100622 530703137968357678621835 := by
  unfold tailWord_3100622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14136121871622939115444015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75392649981989008615701413 14136121871622939115444015)
  ·
    refine ⟨21204182807434408673166023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14136121871622939115444015 21204182807434408673166023)
    ·
      refine ⟨31806274211151613009749035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21204182807434408673166023 31806274211151613009749035)
      ·
        refine ⟨47709411316727419514623553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31806274211151613009749035 47709411316727419514623553)
        ·
          refine ⟨35782058487545564635967665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47709411316727419514623553 35782058487545564635967665)
          ·
            refine ⟨26836543865659173476975749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35782058487545564635967665 26836543865659173476975749)
            ·
              refine ⟨5031851974811095026932953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26836543865659173476975749 5031851974811095026932953)
              ·
                refine ⟨3773888981108321270199715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031851974811095026932953 3773888981108321270199715)
                ·
                  refine ⟨5660833471662481905299573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773888981108321270199715 5660833471662481905299573)
                  ·
                    refine ⟨530703137968357678621835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5660833471662481905299573 530703137968357678621835)
                    ·
                      rfl

theorem cell23_3100622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_3100622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100622 prefixEnd_3100622 := by exact prefixLift 3100622
  have htrace : WordTrace (prefixWord ++ tailWord_3100622) baseStart_3100622 baseEnd_3100622 := by
    simpa [prefixWord, tailWord_3100622, baseEnd_3100622] using wordTrace_append hprefix tailTrace_3100622
  have hstable : (prefixWord ++ tailWord_3100622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100622).length < 2 ^ (prefixWord ++ tailWord_3100622).sum := by decide
  have hdescent : baseEnd_3100622 < baseStart_3100622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100630 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3100630 : Nat := 118140960795 + 3100630 * 2 ^ 59
def prefixEnd_3100630 : Nat := 4983230072969 + 3 ^ 40 * 3100630 * 2
def baseEnd_3100630 : Nat := 530704507250103001521823

theorem tailTrace_3100630 : CollatzResearch.WordTrace tailWord_3100630 prefixEnd_3100630 530704507250103001521823 := by
  unfold tailWord_3100630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068079172309658143115209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75392844504636353526562229 7068079172309658143115209)
  ·
    refine ⟨5301059379232243607336407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7068079172309658143115209 5301059379232243607336407)
    ·
      refine ⟨7951589068848365411004611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5301059379232243607336407 7951589068848365411004611)
      ·
        refine ⟨11927383603272548116506917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951589068848365411004611 11927383603272548116506917)
        ·
          refine ⟨2236384425613602771845047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11927383603272548116506917 2236384425613602771845047)
          ·
            refine ⟨3354576638420404157767571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236384425613602771845047 3354576638420404157767571)
            ·
              refine ⟨5031864957630606236651357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354576638420404157767571 5031864957630606236651357)
              ·
                refine ⟨1886949359111477338744259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5031864957630606236651357 1886949359111477338744259)
                ·
                  refine ⟨2830424038667216008116389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886949359111477338744259 2830424038667216008116389)
                  ·
                    refine ⟨530704507250103001521823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830424038667216008116389 530704507250103001521823)
                    ·
                      rfl

theorem cell23_3100630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3100630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100630 prefixEnd_3100630 := by exact prefixLift 3100630
  have htrace : WordTrace (prefixWord ++ tailWord_3100630) baseStart_3100630 baseEnd_3100630 := by
    simpa [prefixWord, tailWord_3100630, baseEnd_3100630] using wordTrace_append hprefix tailTrace_3100630
  have hstable : (prefixWord ++ tailWord_3100630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100630).length < 2 ^ (prefixWord ++ tailWord_3100630).sum := by decide
  have hdescent : baseEnd_3100630 < baseStart_3100630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100653 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3100653 : Nat := 118140960795 + 3100653 * 2 ^ 59
def prefixEnd_3100653 : Nat := 4983230072969 + 3 ^ 40 * 3100653 * 2
def baseEnd_3100653 : Nat := 1592125331805362414577863

theorem tailTrace_3100653 : CollatzResearch.WordTrace tailWord_3100653 prefixEnd_3100653 1592125331805362414577863 := by
  unfold tailWord_3100653
  simp only [CollatzResearch.WordTrace]
  refine ⟨113090105635871205217930613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75393403757247470145287075 113090105635871205217930613)
  ·
    refine ⟨10602197403362925489180995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113090105635871205217930613 10602197403362925489180995)
    ·
      refine ⟨15903296105044388233771493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10602197403362925489180995 15903296105044388233771493)
      ·
        refine ⟨2981868019695822793832155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15903296105044388233771493 2981868019695822793832155)
        ·
          refine ⟨4472802029543734190748233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981868019695822793832155 4472802029543734190748233)
          ·
            refine ⟨3354601522157800643061175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4472802029543734190748233 3354601522157800643061175)
            ·
              refine ⟨5031902283236700964591763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354601522157800643061175 5031902283236700964591763)
              ·
                refine ⟨7547853424855051446887645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031902283236700964591763 7547853424855051446887645)
                ·
                  refine ⟨2830445034320644292582867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7547853424855051446887645 2830445034320644292582867)
                  ·
                    refine ⟨4245667551480966438874301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830445034320644292582867 4245667551480966438874301)
                    ·
                      refine ⟨1592125331805362414577863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245667551480966438874301 1592125331805362414577863)
                      ·
                        rfl

theorem cell23_3100653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3100653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100653 prefixEnd_3100653 := by exact prefixLift 3100653
  have htrace : WordTrace (prefixWord ++ tailWord_3100653) baseStart_3100653 baseEnd_3100653 := by
    simpa [prefixWord, tailWord_3100653, baseEnd_3100653] using wordTrace_append hprefix tailTrace_3100653
  have hstable : (prefixWord ++ tailWord_3100653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100653).length < 2 ^ (prefixWord ++ tailWord_3100653).sum := by decide
  have hdescent : baseEnd_3100653 < baseStart_3100653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100665 : List Nat := [1, 2, 1, 3, 1, 5, 2, 8]
def baseStart_3100665 : Nat := 118140960795 + 3100665 * 2 ^ 59
def prefixEnd_3100665 : Nat := 4983230072969 + 3 ^ 40 * 3100665 * 2
def baseEnd_3100665 : Nat := 58967833095304309912141

theorem tailTrace_3100665 : CollatzResearch.WordTrace tailWord_3100665 prefixEnd_3100665 58967833095304309912141 := by
  unfold tailWord_3100665
  simp only [CollatzResearch.WordTrace]
  refine ⟨113090543311827731267367449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75393695541218487511578299 113090543311827731267367449)
  ·
    refine ⟨84817907483870798450525587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113090543311827731267367449 84817907483870798450525587)
    ·
      refine ⟨127226861225806197675788381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84817907483870798450525587 127226861225806197675788381)
      ·
        refine ⟨47710072959677324128420643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127226861225806197675788381 47710072959677324128420643)
        ·
          refine ⟨71565109439515986192630965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47710072959677324128420643 71565109439515986192630965)
          ·
            refine ⟨6709229009954623705559153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71565109439515986192630965 6709229009954623705559153)
            ·
              refine ⟨5031921757465967779169365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6709229009954623705559153 5031921757465967779169365)
              ·
                refine ⟨58967833095304309912141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5031921757465967779169365 58967833095304309912141)
                ·
                  rfl

theorem cell23_3100665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 8].length) (baseStart_3100665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100665 prefixEnd_3100665 := by exact prefixLift 3100665
  have htrace : WordTrace (prefixWord ++ tailWord_3100665) baseStart_3100665 baseEnd_3100665 := by
    simpa [prefixWord, tailWord_3100665, baseEnd_3100665] using wordTrace_append hprefix tailTrace_3100665
  have hstable : (prefixWord ++ tailWord_3100665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100665).length < 2 ^ (prefixWord ++ tailWord_3100665).sum := by decide
  have hdescent : baseEnd_3100665 < baseStart_3100665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100669 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_3100669 : Nat := 118140960795 + 3100669 * 2 ^ 59
def prefixEnd_3100669 : Nat := 4983230072969 + 3 ^ 40 * 3100669 * 2
def baseEnd_3100669 : Nat := 530711182498611450659263

theorem tailTrace_3100669 : CollatzResearch.WordTrace tailWord_3100669 prefixEnd_3100669 530711182498611450659263 := by
  unfold tailWord_3100669
  simp only [CollatzResearch.WordTrace]
  refine ⟨113090689203813239950513061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75393792802542159967008707 113090689203813239950513061)
  ·
    refine ⟨21204504225714982490721199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113090689203813239950513061 21204504225714982490721199)
    ·
      refine ⟨31806756338572473736081799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21204504225714982490721199 31806756338572473736081799)
      ·
        refine ⟨47710134507858710604122699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31806756338572473736081799 47710134507858710604122699)
        ·
          refine ⟨71565201761788065906184049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47710134507858710604122699 71565201761788065906184049)
          ·
            refine ⟨53673901321341049429638037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71565201761788065906184049 53673901321341049429638037)
            ·
              refine ⟨2515964124437861692014283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53673901321341049429638037 2515964124437861692014283)
              ·
                refine ⟨3773946186656792538021425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515964124437861692014283 3773946186656792538021425)
                ·
                  refine ⟨2830459639992594403516069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3773946186656792538021425 2830459639992594403516069)
                  ·
                    refine ⟨530711182498611450659263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830459639992594403516069 530711182498611450659263)
                    ·
                      rfl

theorem cell23_3100669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_3100669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100669 prefixEnd_3100669 := by exact prefixLift 3100669
  have htrace : WordTrace (prefixWord ++ tailWord_3100669) baseStart_3100669 baseEnd_3100669 := by
    simpa [prefixWord, tailWord_3100669, baseEnd_3100669] using wordTrace_append hprefix tailTrace_3100669
  have hstable : (prefixWord ++ tailWord_3100669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100669).length < 2 ^ (prefixWord ++ tailWord_3100669).sum := by decide
  have hdescent : baseEnd_3100669 < baseStart_3100669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100675 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 3]
def baseStart_3100675 : Nat := 118140960795 + 3100675 * 2 ^ 59
def prefixEnd_3100675 : Nat := 4983230072969 + 3 ^ 40 * 3100675 * 2
def baseEnd_3100675 : Nat := 1592136628379761328502761

theorem tailTrace_3100675 : CollatzResearch.WordTrace tailWord_3100675 prefixEnd_3100675 1592136628379761328502761 := by
  unfold tailWord_3100675
  simp only [CollatzResearch.WordTrace]
  refine ⟨113090908041791502975231479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75393938694527668650154319 113090908041791502975231479)
  ·
    refine ⟨169636362062687254462847219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113090908041791502975231479 169636362062687254462847219)
    ·
      refine ⟨254454543094030881694270829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169636362062687254462847219 254454543094030881694270829)
      ·
        refine ⟨95420453660261580635351561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254454543094030881694270829 95420453660261580635351561)
        ·
          refine ⟨71565340245196185476513671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95420453660261580635351561 71565340245196185476513671)
          ·
            refine ⟨107348010367794278214770507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71565340245196185476513671 107348010367794278214770507)
            ·
              refine ⟨161022015551691417322155761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107348010367794278214770507 161022015551691417322155761)
              ·
                refine ⟨120766511663768562991616821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161022015551691417322155761 120766511663768562991616821)
                ·
                  refine ⟨11321860468478302780464077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120766511663768562991616821 11321860468478302780464077)
                  ·
                    refine ⟨4245697675679363542674029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11321860468478302780464077 4245697675679363542674029)
                    ·
                      refine ⟨1592136628379761328502761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245697675679363542674029 1592136628379761328502761)
                      ·
                        rfl

theorem cell23_3100675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_3100675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100675 prefixEnd_3100675 := by exact prefixLift 3100675
  have htrace : WordTrace (prefixWord ++ tailWord_3100675) baseStart_3100675 baseEnd_3100675 := by
    simpa [prefixWord, tailWord_3100675, baseEnd_3100675] using wordTrace_append hprefix tailTrace_3100675
  have hstable : (prefixWord ++ tailWord_3100675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100675).length < 2 ^ (prefixWord ++ tailWord_3100675).sum := by decide
  have hdescent : baseEnd_3100675 < baseStart_3100675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100679 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3100679 : Nat := 118140960795 + 3100679 * 2 ^ 59
def prefixEnd_3100679 : Nat := 4983230072969 + 3 ^ 40 * 3100679 * 2
def baseEnd_3100679 : Nat := 1592138682302379312852743

theorem tailTrace_3100679 : CollatzResearch.WordTrace tailWord_3100679 prefixEnd_3100679 1592138682302379312852743 := by
  unfold tailWord_3100679
  simp only [CollatzResearch.WordTrace]
  refine ⟨113091053933777011658377091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75394035955851341105584727 113091053933777011658377091)
  ·
    refine ⟨169636580900665517487565637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113091053933777011658377091 169636580900665517487565637)
    ·
      refine ⟨31806858918874784528918557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169636580900665517487565637 31806858918874784528918557)
      ·
        refine ⟨11927572094578044198344459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31806858918874784528918557 11927572094578044198344459)
        ·
          refine ⟨17891358141867066297516689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11927572094578044198344459 17891358141867066297516689)
          ·
            refine ⟨13418518606400299723137517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17891358141867066297516689 13418518606400299723137517)
            ·
              refine ⟨5031944477400112396176569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13418518606400299723137517 5031944477400112396176569)
              ·
                refine ⟨3773958358050084297132427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031944477400112396176569 3773958358050084297132427)
                ·
                  refine ⟨5660937537075126445698641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773958358050084297132427 5660937537075126445698641)
                  ·
                    refine ⟨4245703152806344834273981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5660937537075126445698641 4245703152806344834273981)
                    ·
                      refine ⟨1592138682302379312852743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245703152806344834273981 1592138682302379312852743)
                      ·
                        rfl

theorem cell23_3100679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3100679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100679 prefixEnd_3100679 := by exact prefixLift 3100679
  have htrace : WordTrace (prefixWord ++ tailWord_3100679) baseStart_3100679 baseEnd_3100679 := by
    simpa [prefixWord, tailWord_3100679, baseEnd_3100679] using wordTrace_append hprefix tailTrace_3100679
  have hstable : (prefixWord ++ tailWord_3100679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100679).length < 2 ^ (prefixWord ++ tailWord_3100679).sum := by decide
  have hdescent : baseEnd_3100679 < baseStart_3100679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100709 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_3100709 : Nat := 118140960795 + 3100709 * 2 ^ 59
def prefixEnd_3100709 : Nat := 4983230072969 + 3 ^ 40 * 3100709 * 2
def baseEnd_3100709 : Nat := 1592154086722014195477605

theorem tailTrace_3100709 : CollatzResearch.WordTrace tailWord_3100709 prefixEnd_3100709 1592154086722014195477605 := by
  unfold tailWord_3100709
  simp only [CollatzResearch.WordTrace]
  refine ⟨113092148123668326781969181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75394765415778884521312787 113092148123668326781969181)
  ·
    refine ⟨42409555546375622543238443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113092148123668326781969181 42409555546375622543238443)
    ·
      refine ⟨63614333319563433814857665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42409555546375622543238443 63614333319563433814857665)
      ·
        refine ⟨47710749989672575361143249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63614333319563433814857665 47710749989672575361143249)
        ·
          refine ⟨35783062492254431520857437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47710749989672575361143249 35783062492254431520857437)
          ·
            refine ⟨13418648434595411820321539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35783062492254431520857437 13418648434595411820321539)
            ·
              refine ⟨20127972651893117730482309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13418648434595411820321539 20127972651893117730482309)
              ·
                refine ⟨3773994872229959574465433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20127972651893117730482309 3773994872229959574465433)
                ·
                  refine ⟨2830496154172469680849075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3773994872229959574465433 2830496154172469680849075)
                  ·
                    refine ⟨4245744231258704521273613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830496154172469680849075 4245744231258704521273613)
                    ·
                      refine ⟨1592154086722014195477605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245744231258704521273613 1592154086722014195477605)
                      ·
                        rfl

theorem cell23_3100709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_3100709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100709 prefixEnd_3100709 := by exact prefixLift 3100709
  have htrace : WordTrace (prefixWord ++ tailWord_3100709) baseStart_3100709 baseEnd_3100709 := by
    simpa [prefixWord, tailWord_3100709, baseEnd_3100709] using wordTrace_append hprefix tailTrace_3100709
  have hstable : (prefixWord ++ tailWord_3100709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100709).length < 2 ^ (prefixWord ++ tailWord_3100709).sum := by decide
  have hdescent : baseEnd_3100709 < baseStart_3100709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100725 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3100725 : Nat := 118140960795 + 3100725 * 2 ^ 59
def prefixEnd_3100725 : Nat := 4983230072969 + 3 ^ 40 * 3100725 * 2
def baseEnd_3100725 : Nat := 530720767470828710959177

theorem tailTrace_3100725 : CollatzResearch.WordTrace tailWord_3100725 prefixEnd_3100725 530720767470828710959177 := by
  unfold tailWord_3100725
  simp only [CollatzResearch.WordTrace]
  refine ⟨113092731691610361514551629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75395154461073574343034419 113092731691610361514551629)
  ·
    refine ⟨42409774384353885567956861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113092731691610361514551629 42409774384353885567956861)
    ·
      refine ⟨15903665394132707087983823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42409774384353885567956861 15903665394132707087983823)
      ·
        refine ⟨23855498091199060631975735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15903665394132707087983823 23855498091199060631975735)
        ·
          refine ⟨35783247136798590947963603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23855498091199060631975735 35783247136798590947963603)
          ·
            refine ⟨53674870705197886421945405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35783247136798590947963603 53674870705197886421945405)
            ·
              refine ⟨20128076514449207408229527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53674870705197886421945405 20128076514449207408229527)
              ·
                refine ⟨30192114771673811112344291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20128076514449207408229527 30192114771673811112344291)
                ·
                  refine ⟨45288172157510716668516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30192114771673811112344291 45288172157510716668516437)
                  ·
                    refine ⟨530720767470828710959177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45288172157510716668516437 530720767470828710959177)
                    ·
                      rfl

theorem cell23_3100725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3100725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100725 prefixEnd_3100725 := by exact prefixLift 3100725
  have htrace : WordTrace (prefixWord ++ tailWord_3100725) baseStart_3100725 baseEnd_3100725 := by
    simpa [prefixWord, tailWord_3100725, baseEnd_3100725] using wordTrace_append hprefix tailTrace_3100725
  have hstable : (prefixWord ++ tailWord_3100725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100725).length < 2 ^ (prefixWord ++ tailWord_3100725).sum := by decide
  have hdescent : baseEnd_3100725 < baseStart_3100725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100726 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3100726 : Nat := 118140960795 + 3100726 * 2 ^ 59
def prefixEnd_3100726 : Nat := 4983230072969 + 3 ^ 40 * 3100726 * 2
def baseEnd_3100726 : Nat := 1592162815893140628965027

theorem tailTrace_3100726 : CollatzResearch.WordTrace tailWord_3100726 prefixEnd_3100726 1592162815893140628965027 := by
  unfold tailWord_3100726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068298010287921167833627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75395178776404492456892021 7068298010287921167833627)
  ·
    refine ⟨10602447015431881751750441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7068298010287921167833627 10602447015431881751750441)
    ·
      refine ⟨7951835261573911313812831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10602447015431881751750441 7951835261573911313812831)
      ·
        refine ⟨11927752892360866970719247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951835261573911313812831 11927752892360866970719247)
        ·
          refine ⟨17891629338541300456078871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11927752892360866970719247 17891629338541300456078871)
          ·
            refine ⟨26837444007811950684118307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17891629338541300456078871 26837444007811950684118307)
            ·
              refine ⟨40256166011717926026177461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26837444007811950684118307 40256166011717926026177461)
              ·
                refine ⟨3774015563598555564954137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40256166011717926026177461 3774015563598555564954137)
                ·
                  refine ⟨2830511672698916673715603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3774015563598555564954137 2830511672698916673715603)
                  ·
                    refine ⟨4245767509048375010573405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830511672698916673715603 4245767509048375010573405)
                    ·
                      refine ⟨1592162815893140628965027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245767509048375010573405 1592162815893140628965027)
                      ·
                        rfl

theorem cell23_3100726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3100726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100726 prefixEnd_3100726 := by exact prefixLift 3100726
  have htrace : WordTrace (prefixWord ++ tailWord_3100726) baseStart_3100726 baseEnd_3100726 := by
    simpa [prefixWord, tailWord_3100726, baseEnd_3100726] using wordTrace_append hprefix tailTrace_3100726
  have hstable : (prefixWord ++ tailWord_3100726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100726).length < 2 ^ (prefixWord ++ tailWord_3100726).sum := by decide
  have hdescent : baseEnd_3100726 < baseStart_3100726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100735 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_3100735 : Nat := 118140960795 + 3100735 * 2 ^ 59
def prefixEnd_3100735 : Nat := 4983230072969 + 3 ^ 40 * 3100735 * 2
def baseEnd_3100735 : Nat := 1592167437219031093752485

theorem tailTrace_3100735 : CollatzResearch.WordTrace tailWord_3100735 prefixEnd_3100735 1592167437219031093752485 := by
  unfold tailWord_3100735
  simp only [CollatzResearch.WordTrace]
  refine ⟨113093096421574133222415659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75395397614382755481610439 113093096421574133222415659)
  ·
    refine ⟨169639644632361199833623489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113093096421574133222415659 169639644632361199833623489)
    ·
      refine ⟨127229733474270899875217617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169639644632361199833623489 127229733474270899875217617)
      ·
        refine ⟨95422300105703174906413213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127229733474270899875217617 95422300105703174906413213)
        ·
          refine ⟨35783362539638690589904955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95422300105703174906413213 35783362539638690589904955)
          ·
            refine ⟨53675043809458035884857433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35783362539638690589904955 53675043809458035884857433)
            ·
              refine ⟨40256282857093526913643075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53675043809458035884857433 40256282857093526913643075)
              ·
                refine ⟨60384424285640290370464613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40256282857093526913643075 60384424285640290370464613)
                ·
                  refine ⟨11322079553557554444462115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60384424285640290370464613 11322079553557554444462115)
                  ·
                    refine ⟨16983119330336331666693173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11322079553557554444462115 16983119330336331666693173)
                    ·
                      refine ⟨1592167437219031093752485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16983119330336331666693173 1592167437219031093752485)
                      ·
                        rfl

theorem cell23_3100735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_3100735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100735 prefixEnd_3100735 := by exact prefixLift 3100735
  have htrace : WordTrace (prefixWord ++ tailWord_3100735) baseStart_3100735 baseEnd_3100735 := by
    simpa [prefixWord, tailWord_3100735, baseEnd_3100735] using wordTrace_append hprefix tailTrace_3100735
  have hstable : (prefixWord ++ tailWord_3100735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100735).length < 2 ^ (prefixWord ++ tailWord_3100735).sum := by decide
  have hdescent : baseEnd_3100735 < baseStart_3100735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100745 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_3100745 : Nat := 118140960795 + 3100745 * 2 ^ 59
def prefixEnd_3100745 : Nat := 4983230072969 + 3 ^ 40 * 3100745 * 2
def baseEnd_3100745 : Nat := 1592172572025576054627439

theorem tailTrace_3100745 : CollatzResearch.WordTrace tailWord_3100745 prefixEnd_3100745 1592172572025576054627439 := by
  unfold tailWord_3100745
  simp only [CollatzResearch.WordTrace]
  refine ⟨113093461151537904930279689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75395640767691936620186459 113093461151537904930279689)
  ·
    refine ⟨84820095863653428697709767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113093461151537904930279689 84820095863653428697709767)
    ·
      refine ⟨127230143795480143046564651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84820095863653428697709767 127230143795480143046564651)
      ·
        refine ⟨190845215693220214569846977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127230143795480143046564651 190845215693220214569846977)
        ·
          refine ⟨143133911769915160927385233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190845215693220214569846977 143133911769915160927385233)
          ·
            refine ⟨107350433827436370695538925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143133911769915160927385233 107350433827436370695538925)
            ·
              refine ⟨40256412685288639010827097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107350433827436370695538925 40256412685288639010827097)
              ·
                refine ⟨30192309513966479258120323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40256412685288639010827097 30192309513966479258120323)
                ·
                  refine ⟨45288464270949718887180485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30192309513966479258120323 45288464270949718887180485)
                  ·
                    refine ⟨8491587050803072291346341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45288464270949718887180485 8491587050803072291346341)
                    ·
                      refine ⟨1592172572025576054627439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8491587050803072291346341 1592172572025576054627439)
                      ·
                        rfl

theorem cell23_3100745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_3100745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100745 prefixEnd_3100745 := by exact prefixLift 3100745
  have htrace : WordTrace (prefixWord ++ tailWord_3100745) baseStart_3100745 baseEnd_3100745 := by
    simpa [prefixWord, tailWord_3100745, baseEnd_3100745] using wordTrace_append hprefix tailTrace_3100745
  have hstable : (prefixWord ++ tailWord_3100745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100745).length < 2 ^ (prefixWord ++ tailWord_3100745).sum := by decide
  have hdescent : baseEnd_3100745 < baseStart_3100745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100783 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 2, 2, 2]
def baseStart_3100783 : Nat := 118140960795 + 3100783 * 2 ^ 59
def prefixEnd_3100783 : Nat := 4983230072969 + 3 ^ 40 * 3100783 * 2
def baseEnd_3100783 : Nat := 1592192084290446905952265

theorem tailTrace_3100783 : CollatzResearch.WordTrace tailWord_3100783 prefixEnd_3100783 1592192084290446905952265 := by
  unfold tailWord_3100783
  simp only [CollatzResearch.WordTrace]
  refine ⟨113094847125400237420163003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75396564750266824946775335 113094847125400237420163003)
  ·
    refine ⟨169642270688100356130244505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113094847125400237420163003 169642270688100356130244505)
    ·
      refine ⟨127231703016075267097683379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169642270688100356130244505 127231703016075267097683379)
      ·
        refine ⟨190847554524112900646525069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127231703016075267097683379 190847554524112900646525069)
        ·
          refine ⟨71567832946542337742446901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190847554524112900646525069 71567832946542337742446901)
          ·
            refine ⟨6709484338738344163354397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71567832946542337742446901 6709484338738344163354397)
            ·
              refine ⟨2516056627026879061257899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6709484338738344163354397 2516056627026879061257899)
              ·
                refine ⟨3774084940540318591886849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516056627026879061257899 3774084940540318591886849)
                ·
                  refine ⟨2830563705405238943915137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3774084940540318591886849 2830563705405238943915137)
                  ·
                    refine ⟨2122922779053929207936353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2830563705405238943915137 2122922779053929207936353)
                    ·
                      refine ⟨1592192084290446905952265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2122922779053929207936353 1592192084290446905952265)
                      ·
                        rfl

theorem cell23_3100783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 2, 2].length) (baseStart_3100783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100783 prefixEnd_3100783 := by exact prefixLift 3100783
  have htrace : WordTrace (prefixWord ++ tailWord_3100783) baseStart_3100783 baseEnd_3100783 := by
    simpa [prefixWord, tailWord_3100783, baseEnd_3100783] using wordTrace_append hprefix tailTrace_3100783
  have hstable : (prefixWord ++ tailWord_3100783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100783).length < 2 ^ (prefixWord ++ tailWord_3100783).sum := by decide
  have hdescent : baseEnd_3100783 < baseStart_3100783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100785 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_3100785 : Nat := 118140960795 + 3100785 * 2 ^ 59
def prefixEnd_3100785 : Nat := 4983230072969 + 3 ^ 40 * 3100785 * 2
def baseEnd_3100785 : Nat := 530731037083918632709085

theorem tailTrace_3100785 : CollatzResearch.WordTrace tailWord_3100785 prefixEnd_3100785 530731037083918632709085 := by
  unfold tailWord_3100785
  simp only [CollatzResearch.WordTrace]
  refine ⟨113094920071392991761735809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75396613380928661174490539 113094920071392991761735809)
  ·
    refine ⟨84821190053544743821301857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113094920071392991761735809 84821190053544743821301857)
    ·
      refine ⟨63615892540158557865976393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84821190053544743821301857 63615892540158557865976393)
      ·
        refine ⟨47711919405118918399482295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63615892540158557865976393 47711919405118918399482295)
        ·
          refine ⟨71567879107678377599223443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47711919405118918399482295 71567879107678377599223443)
          ·
            refine ⟨107351818661517566398835165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71567879107678377599223443 107351818661517566398835165)
            ·
              refine ⟨40256931998069087399563187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107351818661517566398835165 40256931998069087399563187)
              ·
                refine ⟨60385397997103631099344781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40256931998069087399563187 60385397997103631099344781)
                ·
                  refine ⟨22644524248913861662254293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60385397997103631099344781 22644524248913861662254293)
                  ·
                    refine ⟨530731037083918632709085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22644524248913861662254293 530731037083918632709085)
                    ·
                      rfl

theorem cell23_3100785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_3100785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100785 prefixEnd_3100785 := by exact prefixLift 3100785
  have htrace : WordTrace (prefixWord ++ tailWord_3100785) baseStart_3100785 baseEnd_3100785 := by
    simpa [prefixWord, tailWord_3100785, baseEnd_3100785] using wordTrace_append hprefix tailTrace_3100785
  have hstable : (prefixWord ++ tailWord_3100785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100785).length < 2 ^ (prefixWord ++ tailWord_3100785).sum := by decide
  have hdescent : baseEnd_3100785 < baseStart_3100785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100795 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_3100795 : Nat := 118140960795 + 3100795 * 2 ^ 59
def prefixEnd_3100795 : Nat := 4983230072969 + 3 ^ 40 * 3100795 * 2
def baseEnd_3100795 : Nat := 1592198246058300859002209

theorem tailTrace_3100795 : CollatzResearch.WordTrace tailWord_3100795 prefixEnd_3100795 1592198246058300859002209 := by
  unfold tailWord_3100795
  simp only [CollatzResearch.WordTrace]
  refine ⟨113095284801356763469599839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75396856534237842313066559 113095284801356763469599839)
  ·
    refine ⟨169642927202035145204399759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113095284801356763469599839 169642927202035145204399759)
    ·
      refine ⟨254464390803052717806599639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169642927202035145204399759 254464390803052717806599639)
      ·
        refine ⟨381696586204579076709899459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254464390803052717806599639 381696586204579076709899459)
        ·
          refine ⟨572544879306868615064849189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381696586204579076709899459 572544879306868615064849189)
          ·
            refine ⟨107352164870037865324659223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 572544879306868615064849189 107352164870037865324659223)
            ·
              refine ⟨161028247305056797986988835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107352164870037865324659223 161028247305056797986988835)
              ·
                refine ⟨241542370957585196980483253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161028247305056797986988835 241542370957585196980483253)
                ·
                  refine ⟨22644597277273612216920305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241542370957585196980483253 22644597277273612216920305)
                  ·
                    refine ⟨16983447957955209162690229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22644597277273612216920305 16983447957955209162690229)
                    ·
                      refine ⟨1592198246058300859002209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16983447957955209162690229 1592198246058300859002209)
                      ·
                        rfl

theorem cell23_3100795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_3100795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100795 prefixEnd_3100795 := by exact prefixLift 3100795
  have htrace : WordTrace (prefixWord ++ tailWord_3100795) baseStart_3100795 baseEnd_3100795 := by
    simpa [prefixWord, tailWord_3100795, baseEnd_3100795] using wordTrace_append hprefix tailTrace_3100795
  have hstable : (prefixWord ++ tailWord_3100795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100795).length < 2 ^ (prefixWord ++ tailWord_3100795).sum := by decide
  have hdescent : baseEnd_3100795 < baseStart_3100795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100859 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 3]
def baseStart_3100859 : Nat := 118140960795 + 3100859 * 2 ^ 59
def prefixEnd_3100859 : Nat := 4983230072969 + 3 ^ 40 * 3100859 * 2
def baseEnd_3100859 : Nat := 1592231108820188608601915

theorem tailTrace_3100859 : CollatzResearch.WordTrace tailWord_3100859 prefixEnd_3100859 1592231108820188608601915 := by
  unfold tailWord_3100859
  simp only [CollatzResearch.WordTrace]
  refine ⟨113097619073124902399929631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75398412715416601599953087 113097619073124902399929631)
  ·
    refine ⟨169646428609687353599894447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113097619073124902399929631 169646428609687353599894447)
    ·
      refine ⟨254469642914531030399841671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169646428609687353599894447 254469642914531030399841671)
      ·
        refine ⟨381704464371796545599762507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254469642914531030399841671 381704464371796545599762507)
        ·
          refine ⟨572556696557694818399643761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381704464371796545599762507 572556696557694818399643761)
          ·
            refine ⟨429417522418271113799732821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572556696557694818399643761 429417522418271113799732821)
            ·
              refine ⟨5032236590839114614840619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 429417522418271113799732821 5032236590839114614840619)
              ·
                refine ⟨7548354886258671922260929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032236590839114614840619 7548354886258671922260929)
                ·
                  refine ⟨5661266164694003941695697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7548354886258671922260929 5661266164694003941695697)
                  ·
                    refine ⟨4245949623520502956271773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661266164694003941695697 4245949623520502956271773)
                    ·
                      refine ⟨1592231108820188608601915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4245949623520502956271773 1592231108820188608601915)
                      ·
                        rfl

theorem cell23_3100859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 3].length) (baseStart_3100859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100859 prefixEnd_3100859 := by exact prefixLift 3100859
  have htrace : WordTrace (prefixWord ++ tailWord_3100859) baseStart_3100859 baseEnd_3100859 := by
    simpa [prefixWord, tailWord_3100859, baseEnd_3100859] using wordTrace_append hprefix tailTrace_3100859
  have hstable : (prefixWord ++ tailWord_3100859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100859).length < 2 ^ (prefixWord ++ tailWord_3100859).sum := by decide
  have hdescent : baseEnd_3100859 < baseStart_3100859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100906 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3100906 : Nat := 118140960795 + 3100906 * 2 ^ 59
def prefixEnd_3100906 : Nat := 4983230072969 + 3 ^ 40 * 3100906 * 2
def baseEnd_3100906 : Nat := 1592255242410949924714199

theorem tailTrace_3100906 : CollatzResearch.WordTrace tailWord_3100906 prefixEnd_3100906 1592255242410949924714199 := by
  unfold tailWord_3100906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28274833325988657356722643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75399555535969752951260381 28274833325988657356722643)
  ·
    refine ⟨42412249988982986035083965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28274833325988657356722643 42412249988982986035083965)
    ·
      refine ⟨15904593745868619763156487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42412249988982986035083965 15904593745868619763156487)
      ·
        refine ⟨23856890618802929644734731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15904593745868619763156487 23856890618802929644734731)
        ·
          refine ⟨35785335928204394467102097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23856890618802929644734731 35785335928204394467102097)
          ·
            refine ⟨26839001946153295850326573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35785335928204394467102097 26839001946153295850326573)
            ·
              refine ⟨10064625729807485943872465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26839001946153295850326573 10064625729807485943872465)
              ·
                refine ⟨7548469297355614457904349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10064625729807485943872465 7548469297355614457904349)
                ·
                  refine ⟨2830675986508355421714131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7548469297355614457904349 2830675986508355421714131)
                  ·
                    refine ⟨4246013979762533132571197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830675986508355421714131 4246013979762533132571197)
                    ·
                      refine ⟨1592255242410949924714199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246013979762533132571197 1592255242410949924714199)
                      ·
                        rfl

theorem cell23_3100906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3100906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100906 prefixEnd_3100906 := by exact prefixLift 3100906
  have htrace : WordTrace (prefixWord ++ tailWord_3100906) baseStart_3100906 baseEnd_3100906 := by
    simpa [prefixWord, tailWord_3100906, baseEnd_3100906] using wordTrace_append hprefix tailTrace_3100906
  have hstable : (prefixWord ++ tailWord_3100906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100906).length < 2 ^ (prefixWord ++ tailWord_3100906).sum := by decide
  have hdescent : baseEnd_3100906 < baseStart_3100906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100926 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_3100926 : Nat := 118140960795 + 3100926 * 2 ^ 59
def prefixEnd_3100926 : Nat := 4983230072969 + 3 ^ 40 * 3100926 * 2
def baseEnd_3100926 : Nat := 530755170674679948821369

theorem tailTrace_3100926 : CollatzResearch.WordTrace tailWord_3100926 prefixEnd_3100926 530755170674679948821369 := by
  unfold tailWord_3100926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137507845485271605327329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75400041842588115228412421 14137507845485271605327329)
  ·
    refine ⟨10603130884113953703995497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14137507845485271605327329 10603130884113953703995497)
    ·
      refine ⟨7952348163085465277996623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10603130884113953703995497 7952348163085465277996623)
      ·
        refine ⟨11928522244628197916994935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7952348163085465277996623 11928522244628197916994935)
        ·
          refine ⟨17892783366942296875492403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11928522244628197916994935 17892783366942296875492403)
          ·
            refine ⟨26839175050413445313238605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17892783366942296875492403 26839175050413445313238605)
            ·
              refine ⟨10064690643905041992464477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26839175050413445313238605 10064690643905041992464477)
              ·
                refine ⟨3774258991464390747174179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10064690643905041992464477 3774258991464390747174179)
                ·
                  refine ⟨5661388487196586120761269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774258991464390747174179 5661388487196586120761269)
                  ·
                    refine ⟨530755170674679948821369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5661388487196586120761269 530755170674679948821369)
                    ·
                      rfl

theorem cell23_3100926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_3100926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100926 prefixEnd_3100926 := by exact prefixLift 3100926
  have htrace : WordTrace (prefixWord ++ tailWord_3100926) baseStart_3100926 baseEnd_3100926 := by
    simpa [prefixWord, tailWord_3100926, baseEnd_3100926] using wordTrace_append hprefix tailTrace_3100926
  have hstable : (prefixWord ++ tailWord_3100926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100926).length < 2 ^ (prefixWord ++ tailWord_3100926).sum := by decide
  have hdescent : baseEnd_3100926 < baseStart_3100926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100939 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 4, 4]
def baseStart_3100939 : Nat := 118140960795 + 3100939 * 2 ^ 59
def prefixEnd_3100939 : Nat := 4983230072969 + 3 ^ 40 * 3100939 * 2
def baseEnd_3100939 : Nat := 530757395757516098533849

theorem tailTrace_3100939 : CollatzResearch.WordTrace tailWord_3100939 prefixEnd_3100939 530757395757516098533849 := by
  unfold tailWord_3100939
  simp only [CollatzResearch.WordTrace]
  refine ⟨113100536912835076062841871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75400357941890050708561247 113100536912835076062841871)
  ·
    refine ⟨169650805369252614094262807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113100536912835076062841871 169650805369252614094262807)
    ·
      refine ⟨254476208053878921141394211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169650805369252614094262807 254476208053878921141394211)
      ·
        refine ⟨381714312080818381712091317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254476208053878921141394211 381714312080818381712091317)
        ·
          refine ⟨35785716757576723285508561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 381714312080818381712091317 35785716757576723285508561)
          ·
            refine ⟨26839287568182542464131421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35785716757576723285508561 26839287568182542464131421)
            ·
              refine ⟨10064732838068453424049283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26839287568182542464131421 10064732838068453424049283)
              ·
                refine ⟨15097099257102680136073925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10064732838068453424049283 15097099257102680136073925)
                ·
                  refine ⟨2830706110706752525513861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15097099257102680136073925 2830706110706752525513861)
                  ·
                    refine ⟨530757395757516098533849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830706110706752525513861 530757395757516098533849)
                    ·
                      rfl

theorem cell23_3100939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 4].length) (baseStart_3100939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100939 prefixEnd_3100939 := by exact prefixLift 3100939
  have htrace : WordTrace (prefixWord ++ tailWord_3100939) baseStart_3100939 baseEnd_3100939 := by
    simpa [prefixWord, tailWord_3100939, baseEnd_3100939] using wordTrace_append hprefix tailTrace_3100939
  have hstable : (prefixWord ++ tailWord_3100939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100939).length < 2 ^ (prefixWord ++ tailWord_3100939).sum := by decide
  have hdescent : baseEnd_3100939 < baseStart_3100939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100949 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_3100949 : Nat := 118140960795 + 3100949 * 2 ^ 59
def prefixEnd_3100949 : Nat := 4983230072969 + 3 ^ 40 * 3100949 * 2
def baseEnd_3100949 : Nat := 1592277322079093256476501

theorem tailTrace_3100949 : CollatzResearch.WordTrace tailWord_3100949 prefixEnd_3100949 1592277322079093256476501 := by
  unfold tailWord_3100949
  simp only [CollatzResearch.WordTrace]
  refine ⟨113100901642798847770705901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75400601095199231847137267 113100901642798847770705901)
  ·
    refine ⟨42412838116049567914014713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113100901642798847770705901 42412838116049567914014713)
    ·
      refine ⟨31809628587037175935511035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42412838116049567914014713 31809628587037175935511035)
      ·
        refine ⟨47714442880555763903266553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31809628587037175935511035 47714442880555763903266553)
        ·
          refine ⟨35785832160416822927449915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47714442880555763903266553 35785832160416822927449915)
          ·
            refine ⟨53678748240625234391174873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35785832160416822927449915 53678748240625234391174873)
            ·
              refine ⟨40259061180468925793381155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53678748240625234391174873 40259061180468925793381155)
              ·
                refine ⟨60388591770703388690071733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40259061180468925793381155 60388591770703388690071733)
                ·
                  refine ⟨5661430478503442689694225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60388591770703388690071733 5661430478503442689694225)
                  ·
                    refine ⟨4246072858877582017270669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661430478503442689694225 4246072858877582017270669)
                    ·
                      refine ⟨1592277322079093256476501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246072858877582017270669 1592277322079093256476501)
                      ·
                        rfl

theorem cell23_3100949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_3100949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100949 prefixEnd_3100949 := by exact prefixLift 3100949
  have htrace : WordTrace (prefixWord ++ tailWord_3100949) baseStart_3100949 baseEnd_3100949 := by
    simpa [prefixWord, tailWord_3100949, baseEnd_3100949] using wordTrace_append hprefix tailTrace_3100949
  have hstable : (prefixWord ++ tailWord_3100949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100949).length < 2 ^ (prefixWord ++ tailWord_3100949).sum := by decide
  have hdescent : baseEnd_3100949 < baseStart_3100949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100952 : List Nat := [2, 1, 2, 3, 1, 2, 2, 10]
def baseStart_3100952 : Nat := 118140960795 + 3100952 * 2 ^ 59
def prefixEnd_3100952 : Nat := 4983230072969 + 3 ^ 40 * 3100952 * 2
def baseEnd_3100952 : Nat := 58973291204483583138481

theorem tailTrace_3100952 : CollatzResearch.WordTrace tailWord_3100952 prefixEnd_3100952 58973291204483583138481 := by
  unfold tailWord_3100952
  simp only [CollatzResearch.WordTrace]
  refine ⟨56550505530893989641532555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75400674041191986188710073 56550505530893989641532555)
  ·
    refine ⟨84825758296340984462298833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56550505530893989641532555 84825758296340984462298833)
    ·
      refine ⟨63619318722255738346724125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84825758296340984462298833 63619318722255738346724125)
      ·
        refine ⟨23857244520845901880021547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63619318722255738346724125 23857244520845901880021547)
        ·
          refine ⟨35785866781268852820032321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23857244520845901880021547 35785866781268852820032321)
          ·
            refine ⟨26839400085951639615024241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35785866781268852820032321 26839400085951639615024241)
            ·
              refine ⟨20129550064463729711268181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26839400085951639615024241 20129550064463729711268181)
              ·
                refine ⟨58973291204483583138481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20129550064463729711268181 58973291204483583138481)
                ·
                  rfl

theorem cell23_3100952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 10].length) (baseStart_3100952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100952 prefixEnd_3100952 := by exact prefixLift 3100952
  have htrace : WordTrace (prefixWord ++ tailWord_3100952) baseStart_3100952 baseEnd_3100952 := by
    simpa [prefixWord, tailWord_3100952, baseEnd_3100952] using wordTrace_append hprefix tailTrace_3100952
  have hstable : (prefixWord ++ tailWord_3100952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100952).length < 2 ^ (prefixWord ++ tailWord_3100952).sum := by decide
  have hdescent : baseEnd_3100952 < baseStart_3100952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100959 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3100959 : Nat := 118140960795 + 3100959 * 2 ^ 59
def prefixEnd_3100959 : Nat := 4983230072969 + 3 ^ 40 * 3100959 * 2
def baseEnd_3100959 : Nat := 1592282456885638217351455

theorem tailTrace_3100959 : CollatzResearch.WordTrace tailWord_3100959 prefixEnd_3100959 1592282456885638217351455 := by
  unfold tailWord_3100959
  simp only [CollatzResearch.WordTrace]
  refine ⟨113101266372762619478569931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75400844248508412985713287 113101266372762619478569931)
  ·
    refine ⟨169651899559143929217854897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113101266372762619478569931 169651899559143929217854897)
    ·
      refine ⟨127238924669357946913391173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169651899559143929217854897 127238924669357946913391173)
      ·
        refine ⟨23857298375504615046260845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127238924669357946913391173 23857298375504615046260845)
        ·
          refine ⟨8946486890814230642347817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23857298375504615046260845 8946486890814230642347817)
          ·
            refine ⟨6709865168110672981760863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8946486890814230642347817 6709865168110672981760863)
            ·
              refine ⟨10064797752166009472641295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6709865168110672981760863 10064797752166009472641295)
              ·
                refine ⟨15097196628249014208961943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10064797752166009472641295 15097196628249014208961943)
                ·
                  refine ⟨22645794942373521313442915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15097196628249014208961943 22645794942373521313442915)
                  ·
                    refine ⟨33968692413560281970164373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22645794942373521313442915 33968692413560281970164373)
                    ·
                      refine ⟨1592282456885638217351455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33968692413560281970164373 1592282456885638217351455)
                      ·
                        rfl

theorem cell23_3100959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3100959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100959 prefixEnd_3100959 := by exact prefixLift 3100959
  have htrace : WordTrace (prefixWord ++ tailWord_3100959) baseStart_3100959 baseEnd_3100959 := by
    simpa [prefixWord, tailWord_3100959, baseEnd_3100959] using wordTrace_append hprefix tailTrace_3100959
  have hstable : (prefixWord ++ tailWord_3100959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100959).length < 2 ^ (prefixWord ++ tailWord_3100959).sum := by decide
  have hdescent : baseEnd_3100959 < baseStart_3100959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100974 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3100974 : Nat := 118140960795 + 3100974 * 2 ^ 59
def prefixEnd_3100974 : Nat := 4983230072969 + 3 ^ 40 * 3100974 * 2
def baseEnd_3100974 : Nat := 1592290159095455658663887

theorem tailTrace_3100974 : CollatzResearch.WordTrace tailWord_3100974 prefixEnd_3100974 1592290159095455658663887 := by
  unfold tailWord_3100974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137726683463534630045747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75401208978472184693577317 14137726683463534630045747)
  ·
    refine ⟨21206590025195301945068621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14137726683463534630045747 21206590025195301945068621)
    ·
      refine ⟨7952471259448238229400733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21206590025195301945068621 7952471259448238229400733)
      ·
        refine ⟨2982176722293089336025275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7952471259448238229400733 2982176722293089336025275)
        ·
          refine ⟨4473265083439634004037913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982176722293089336025275 4473265083439634004037913)
          ·
            refine ⟨3354948812579725503028435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4473265083439634004037913 3354948812579725503028435)
            ·
              refine ⟨5032423218869588254542653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354948812579725503028435 5032423218869588254542653)
              ·
                refine ⟨1887158707076095595453495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5032423218869588254542653 1887158707076095595453495)
                ·
                  refine ⟨2830738060614143393180243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887158707076095595453495 2830738060614143393180243)
                  ·
                    refine ⟨4246107090921215089770365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830738060614143393180243 4246107090921215089770365)
                    ·
                      refine ⟨1592290159095455658663887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246107090921215089770365 1592290159095455658663887)
                      ·
                        rfl

theorem cell23_3100974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3100974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100974 prefixEnd_3100974 := by exact prefixLift 3100974
  have htrace : WordTrace (prefixWord ++ tailWord_3100974) baseStart_3100974 baseEnd_3100974 := by
    simpa [prefixWord, tailWord_3100974, baseEnd_3100974] using wordTrace_append hprefix tailTrace_3100974
  have hstable : (prefixWord ++ tailWord_3100974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100974).length < 2 ^ (prefixWord ++ tailWord_3100974).sum := by decide
  have hdescent : baseEnd_3100974 < baseStart_3100974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100979 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 3]
def baseStart_3100979 : Nat := 118140960795 + 3100979 * 2 ^ 59
def prefixEnd_3100979 : Nat := 4983230072969 + 3 ^ 40 * 3100979 * 2
def baseEnd_3100979 : Nat := 1592292726498728139101363

theorem tailTrace_3100979 : CollatzResearch.WordTrace tailWord_3100979 prefixEnd_3100979 1592292726498728139101363 := by
  unfold tailWord_3100979
  simp only [CollatzResearch.WordTrace]
  refine ⟨113101995832690162894297991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75401330555126775262865327 113101995832690162894297991)
  ·
    refine ⟨169652993749035244341446987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113101995832690162894297991 169652993749035244341446987)
    ·
      refine ⟨254479490623552866512170481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169652993749035244341446987 254479490623552866512170481)
      ·
        refine ⟨190859617967664649884127861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254479490623552866512170481 190859617967664649884127861)
        ·
          refine ⟨17893089184468560926636987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190859617967664649884127861 17893089184468560926636987)
          ·
            refine ⟨26839633776702841389955481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17893089184468560926636987 26839633776702841389955481)
            ·
              refine ⟨20129725332527131042466611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26839633776702841389955481 20129725332527131042466611)
              ·
                refine ⟨30194587998790696563699917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20129725332527131042466611 30194587998790696563699917)
                ·
                  refine ⟨11322970499546511211387469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30194587998790696563699917 11322970499546511211387469)
                  ·
                    refine ⟨4246113937329941704270301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11322970499546511211387469 4246113937329941704270301)
                    ·
                      refine ⟨1592292726498728139101363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246113937329941704270301 1592292726498728139101363)
                      ·
                        rfl

theorem cell23_3100979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_3100979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3100979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3100979 prefixEnd_3100979 := by exact prefixLift 3100979
  have htrace : WordTrace (prefixWord ++ tailWord_3100979) baseStart_3100979 baseEnd_3100979 := by
    simpa [prefixWord, tailWord_3100979, baseEnd_3100979] using wordTrace_append hprefix tailTrace_3100979
  have hstable : (prefixWord ++ tailWord_3100979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100979).length < 2 ^ (prefixWord ++ tailWord_3100979).sum := by decide
  have hdescent : baseEnd_3100979 < baseStart_3100979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101023 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 1, 3, 2]
def baseStart_3101023 : Nat := 118140960795 + 3101023 * 2 ^ 59
def prefixEnd_3101023 : Nat := 4983230072969 + 3 ^ 40 * 3101023 * 2
def baseEnd_3101023 : Nat := 1592315319647525966951161

theorem tailTrace_3101023 : CollatzResearch.WordTrace tailWord_3101023 prefixEnd_3101023 1592315319647525966951161 := by
  unfold tailWord_3101023
  simp only [CollatzResearch.WordTrace]
  refine ⟨113103600644530758408899723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75402400429687172272599815 113103600644530758408899723)
  ·
    refine ⟨169655400966796137613349585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113103600644530758408899723 169655400966796137613349585)
    ·
      refine ⟨127241550725097103210012189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169655400966796137613349585 127241550725097103210012189)
      ·
        refine ⟨47715581521911413703754571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127241550725097103210012189 47715581521911413703754571)
        ·
          refine ⟨71573372282867120555631857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47715581521911413703754571 71573372282867120555631857)
          ·
            refine ⟨53680029212150340416723893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71573372282867120555631857 53680029212150340416723893)
            ·
              refine ⟨5032502738639094414067865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53680029212150340416723893 5032502738639094414067865)
              ·
                refine ⟨3774377053979320810550899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5032502738639094414067865 3774377053979320810550899)
                ·
                  refine ⟨5661565580968981215826349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774377053979320810550899 5661565580968981215826349)
                  ·
                    refine ⟨2123087092863367955934881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5661565580968981215826349 2123087092863367955934881)
                    ·
                      refine ⟨1592315319647525966951161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123087092863367955934881 1592315319647525966951161)
                      ·
                        rfl

theorem cell23_3101023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_3101023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101023 prefixEnd_3101023 := by exact prefixLift 3101023
  have htrace : WordTrace (prefixWord ++ tailWord_3101023) baseStart_3101023 baseEnd_3101023 := by
    simpa [prefixWord, tailWord_3101023, baseEnd_3101023] using wordTrace_append hprefix tailTrace_3101023
  have hstable : (prefixWord ++ tailWord_3101023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101023).length < 2 ^ (prefixWord ++ tailWord_3101023).sum := by decide
  have hdescent : baseEnd_3101023 < baseStart_3101023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101040 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 1, 3, 2]
def baseStart_3101040 : Nat := 118140960795 + 3101040 * 2 ^ 59
def prefixEnd_3101040 : Nat := 4983230072969 + 3 ^ 40 * 3101040 * 2
def baseEnd_3101040 : Nat := 1592324048818652400438583

theorem tailTrace_3101040 : CollatzResearch.WordTrace tailWord_3101040 prefixEnd_3101040 1592324048818652400438583 := by
  unfold tailWord_3101040
  simp only [CollatzResearch.WordTrace]
  refine ⟨56552110342734585156134287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75402813790312780208179049 56552110342734585156134287)
  ·
    refine ⟨84828165514101877734201431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56552110342734585156134287 84828165514101877734201431)
    ·
      refine ⟨127242248271152816601302147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84828165514101877734201431 127242248271152816601302147)
      ·
        refine ⟨190863372406729224901953221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127242248271152816601302147 190863372406729224901953221)
        ·
          refine ⟨35786882326261729669116229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190863372406729224901953221 35786882326261729669116229)
          ·
            refine ⟨6710040436174074312959293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35786882326261729669116229 6710040436174074312959293)
            ·
              refine ⟨2516265163565277867359735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6710040436174074312959293 2516265163565277867359735)
              ·
                refine ⟨3774397745347916801039603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516265163565277867359735 3774397745347916801039603)
                ·
                  refine ⟨5661596618021875201559405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774397745347916801039603 5661596618021875201559405)
                  ·
                    refine ⟨2123098731758203200584777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5661596618021875201559405 2123098731758203200584777)
                    ·
                      refine ⟨1592324048818652400438583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123098731758203200584777 1592324048818652400438583)
                      ·
                        rfl

theorem cell23_3101040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 3, 2].length) (baseStart_3101040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101040 prefixEnd_3101040 := by exact prefixLift 3101040
  have htrace : WordTrace (prefixWord ++ tailWord_3101040) baseStart_3101040 baseEnd_3101040 := by
    simpa [prefixWord, tailWord_3101040, baseEnd_3101040] using wordTrace_append hprefix tailTrace_3101040
  have hstable : (prefixWord ++ tailWord_3101040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101040).length < 2 ^ (prefixWord ++ tailWord_3101040).sum := by decide
  have hdescent : baseEnd_3101040 < baseStart_3101040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101049 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3101049 : Nat := 118140960795 + 3101049 * 2 ^ 59
def prefixEnd_3101049 : Nat := 4983230072969 + 3 ^ 40 * 3101049 * 2
def baseEnd_3101049 : Nat := 1592328670144542865226041

theorem tailTrace_3101049 : CollatzResearch.WordTrace tailWord_3101049 prefixEnd_3101049 1592328670144542865226041 := by
  unfold tailWord_3101049
  simp only [CollatzResearch.WordTrace]
  refine ⟨113104548942436564849346201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75403032628291043232897467 113104548942436564849346201)
  ·
    refine ⟨84828411706827423637009651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113104548942436564849346201 84828411706827423637009651)
    ·
      refine ⟨127242617560241135455514477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84828411706827423637009651 127242617560241135455514477)
      ·
        refine ⟨47715981585090425795817929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127242617560241135455514477 47715981585090425795817929)
        ·
          refine ⟨35786986188817819346863447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47715981585090425795817929 35786986188817819346863447)
          ·
            refine ⟨53680479283226729020295171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35786986188817819346863447 53680479283226729020295171)
            ·
              refine ⟨80520718924840093530442757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53680479283226729020295171 80520718924840093530442757)
              ·
                refine ⟨15097634798407517536958017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80520718924840093530442757 15097634798407517536958017)
                ·
                  refine ⟨11323226098805638152718513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15097634798407517536958017 11323226098805638152718513)
                  ·
                    refine ⟨8492419574104228614538885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11323226098805638152718513 8492419574104228614538885)
                    ·
                      refine ⟨1592328670144542865226041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8492419574104228614538885 1592328670144542865226041)
                      ·
                        rfl

theorem cell23_3101049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3101049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101049 prefixEnd_3101049 := by exact prefixLift 3101049
  have htrace : WordTrace (prefixWord ++ tailWord_3101049) baseStart_3101049 baseEnd_3101049 := by
    simpa [prefixWord, tailWord_3101049, baseEnd_3101049] using wordTrace_append hprefix tailTrace_3101049
  have hstable : (prefixWord ++ tailWord_3101049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101049).length < 2 ^ (prefixWord ++ tailWord_3101049).sum := by decide
  have hdescent : baseEnd_3101049 < baseStart_3101049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101070 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3101070 : Nat := 118140960795 + 3101070 * 2 ^ 59
def prefixEnd_3101070 : Nat := 4983230072969 + 3 ^ 40 * 3101070 * 2
def baseEnd_3101070 : Nat := 1592339453238287283063445

theorem tailTrace_3101070 : CollatzResearch.WordTrace tailWord_3101070 prefixEnd_3101070 1592339453238287283063445 := by
  unfold tailWord_3101070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138164359420060679482583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75403543250240323623907109 14138164359420060679482583)
  ·
    refine ⟨21207246539130091019223875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14138164359420060679482583 21207246539130091019223875)
    ·
      refine ⟨31810869808695136528835813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21207246539130091019223875 31810869808695136528835813)
      ·
        refine ⟨5964538089130338099156715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31810869808695136528835813 5964538089130338099156715)
        ·
          refine ⟨8946807133695507148735073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964538089130338099156715 8946807133695507148735073)
          ·
            refine ⟨6710105350271630361551305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8946807133695507148735073 6710105350271630361551305)
            ·
              refine ⟨5032579012703722771163479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6710105350271630361551305 5032579012703722771163479)
              ·
                refine ⟨7548868519055584156745219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032579012703722771163479 7548868519055584156745219)
                ·
                  refine ⟨11323302778583376235117829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548868519055584156745219 11323302778583376235117829)
                  ·
                    refine ⟨2123119270984383044084593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11323302778583376235117829 2123119270984383044084593)
                    ·
                      refine ⟨1592339453238287283063445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123119270984383044084593 1592339453238287283063445)
                      ·
                        rfl

theorem cell23_3101070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3101070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101070 prefixEnd_3101070 := by exact prefixLift 3101070
  have htrace : WordTrace (prefixWord ++ tailWord_3101070) baseStart_3101070 baseEnd_3101070 := by
    simpa [prefixWord, tailWord_3101070, baseEnd_3101070] using wordTrace_append hprefix tailTrace_3101070
  have hstable : (prefixWord ++ tailWord_3101070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101070).length < 2 ^ (prefixWord ++ tailWord_3101070).sum := by decide
  have hdescent : baseEnd_3101070 < baseStart_3101070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101121 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3101121 : Nat := 118140960795 + 3101121 * 2 ^ 59
def prefixEnd_3101121 : Nat := 4983230072969 + 3 ^ 40 * 3101121 * 2
def baseEnd_3101121 : Nat := 1592365640751666583525711

theorem tailTrace_3101121 : CollatzResearch.WordTrace tailWord_3101121 prefixEnd_3101121 1592365640751666583525711 := by
  unfold tailWord_3101121
  simp only [CollatzResearch.WordTrace]
  refine ⟨113107174998175721145967217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75404783332117147430644811 113107174998175721145967217)
  ·
    refine ⟨84830381248631790859475413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113107174998175721145967217 84830381248631790859475413)
    ·
      refine ⟨1988212060514807598268955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 84830381248631790859475413 1988212060514807598268955)
      ·
        refine ⟨2982318090772211397403433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988212060514807598268955 2982318090772211397403433)
        ·
          refine ⟨2236738568079158548052575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982318090772211397403433 2236738568079158548052575)
          ·
            refine ⟨3355107852118737822078863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236738568079158548052575 3355107852118737822078863)
            ·
              refine ⟨5032661778178106733118295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355107852118737822078863 5032661778178106733118295)
              ·
                refine ⟨7548992667267160099677443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032661778178106733118295 7548992667267160099677443)
                ·
                  refine ⟨11323489000900740149516165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548992667267160099677443 11323489000900740149516165)
                  ·
                    refine ⟨2123154187668888778034281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11323489000900740149516165 2123154187668888778034281)
                    ·
                      refine ⟨1592365640751666583525711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123154187668888778034281 1592365640751666583525711)
                      ·
                        rfl

theorem cell23_3101121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3101121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101121 prefixEnd_3101121 := by exact prefixLift 3101121
  have htrace : WordTrace (prefixWord ++ tailWord_3101121) baseStart_3101121 baseEnd_3101121 := by
    simpa [prefixWord, tailWord_3101121, baseEnd_3101121] using wordTrace_append hprefix tailTrace_3101121
  have hstable : (prefixWord ++ tailWord_3101121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101121).length < 2 ^ (prefixWord ++ tailWord_3101121).sum := by decide
  have hdescent : baseEnd_3101121 < baseStart_3101121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101146 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_3101146 : Nat := 118140960795 + 3101146 * 2 ^ 59
def prefixEnd_3101146 : Nat := 4983230072969 + 3 ^ 40 * 3101146 * 2
def baseEnd_3101146 : Nat := 1592378477768028985713095

theorem tailTrace_3101146 : CollatzResearch.WordTrace tailWord_3101146 prefixEnd_3101146 1592378477768028985713095 := by
  unfold tailWord_3101146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28277021705771287603906823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75405391215390100277084861 28277021705771287603906823)
  ·
    refine ⟨42415532558656931405860235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28277021705771287603906823 42415532558656931405860235)
    ·
      refine ⟨63623298837985397108790353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42415532558656931405860235 63623298837985397108790353)
      ·
        refine ⟨47717474128489047831592765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63623298837985397108790353 47717474128489047831592765)
        ·
          refine ⟨17894052798183392936847287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47717474128489047831592765 17894052798183392936847287)
          ·
            refine ⟨26841079197275089405270931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17894052798183392936847287 26841079197275089405270931)
            ·
              refine ⟨40261618795912634107906397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26841079197275089405270931 40261618795912634107906397)
              ·
                refine ⟨15098107048467237790464899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40261618795912634107906397 15098107048467237790464899)
                ·
                  refine ⟨22647160572700856685697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15098107048467237790464899 22647160572700856685697349)
                  ·
                    refine ⟨4246342607381410628568253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22647160572700856685697349 4246342607381410628568253)
                    ·
                      refine ⟨1592378477768028985713095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246342607381410628568253 1592378477768028985713095)
                      ·
                        rfl

theorem cell23_3101146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_3101146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101146 prefixEnd_3101146 := by exact prefixLift 3101146
  have htrace : WordTrace (prefixWord ++ tailWord_3101146) baseStart_3101146 baseEnd_3101146 := by
    simpa [prefixWord, tailWord_3101146, baseEnd_3101146] using wordTrace_append hprefix tailTrace_3101146
  have hstable : (prefixWord ++ tailWord_3101146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101146).length < 2 ^ (prefixWord ++ tailWord_3101146).sum := by decide
  have hdescent : baseEnd_3101146 < baseStart_3101146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101166 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_3101166 : Nat := 118140960795 + 3101166 * 2 ^ 59
def prefixEnd_3101166 : Nat := 4983230072969 + 3 ^ 40 * 3101166 * 2
def baseEnd_3101166 : Nat := 176932083042346545273667

theorem tailTrace_3101166 : CollatzResearch.WordTrace tailWord_3101166 prefixEnd_3101166 176932083042346545273667 := by
  unfold tailWord_3101166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138602035376586728919419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75405877522008462554236901 14138602035376586728919419)
  ·
    refine ⟨21207903053064880093379129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14138602035376586728919419 21207903053064880093379129)
    ·
      refine ⟨15905927289798660070034347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21207903053064880093379129 15905927289798660070034347)
      ·
        refine ⟨23858890934697990105051521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15905927289798660070034347 23858890934697990105051521)
        ·
          refine ⟨17894168201023492578788641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23858890934697990105051521 17894168201023492578788641)
          ·
            refine ⟨13420626150767619434091481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17894168201023492578788641 13420626150767619434091481)
            ·
              refine ⟨10065469613075714575568611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13420626150767619434091481 10065469613075714575568611)
              ·
                refine ⟨15098204419613571863352917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10065469613075714575568611 15098204419613571863352917)
                ·
                  refine ⟨176932083042346545273667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15098204419613571863352917 176932083042346545273667)
                  ·
                    rfl

theorem cell23_3101166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_3101166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101166 prefixEnd_3101166 := by exact prefixLift 3101166
  have htrace : WordTrace (prefixWord ++ tailWord_3101166) baseStart_3101166 baseEnd_3101166 := by
    simpa [prefixWord, tailWord_3101166, baseEnd_3101166] using wordTrace_append hprefix tailTrace_3101166
  have hstable : (prefixWord ++ tailWord_3101166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101166).length < 2 ^ (prefixWord ++ tailWord_3101166).sum := by decide
  have hdescent : baseEnd_3101166 < baseStart_3101166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101197 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3101197 : Nat := 118140960795 + 3101197 * 2 ^ 59
def prefixEnd_3101197 : Nat := 4983230072969 + 3 ^ 40 * 3101197 * 2
def baseEnd_3101197 : Nat := 1592404665281408286175361

theorem tailTrace_3101197 : CollatzResearch.WordTrace tailWord_3101197 prefixEnd_3101197 1592404665281408286175361 := by
  unfold tailWord_3101197
  simp only [CollatzResearch.WordTrace]
  refine ⟨113109946945900386125733845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75406631297266924083822563 113109946945900386125733845)
  ·
    refine ⟨2651014381544540299821887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 113109946945900386125733845 2651014381544540299821887)
    ·
      refine ⟨3976521572316810449732831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651014381544540299821887 3976521572316810449732831)
      ·
        refine ⟨5964782358475215674599247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976521572316810449732831 5964782358475215674599247)
        ·
          refine ⟨8947173537712823511898871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964782358475215674599247 8947173537712823511898871)
          ·
            refine ⟨13420760306569235267848307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8947173537712823511898871 13420760306569235267848307)
            ·
              refine ⟨20131140459853852901772461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13420760306569235267848307 20131140459853852901772461)
              ·
                refine ⟨7549177672445194838164673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20131140459853852901772461 7549177672445194838164673)
                ·
                  refine ⟨5661883254333896128623505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549177672445194838164673 5661883254333896128623505)
                  ·
                    refine ⟨4246412440750422096467629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661883254333896128623505 4246412440750422096467629)
                    ·
                      refine ⟨1592404665281408286175361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246412440750422096467629 1592404665281408286175361)
                      ·
                        rfl

theorem cell23_3101197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3101197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101197 prefixEnd_3101197 := by exact prefixLift 3101197
  have htrace : WordTrace (prefixWord ++ tailWord_3101197) baseStart_3101197 baseEnd_3101197 := by
    simpa [prefixWord, tailWord_3101197, baseEnd_3101197] using wordTrace_append hprefix tailTrace_3101197
  have hstable : (prefixWord ++ tailWord_3101197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101197).length < 2 ^ (prefixWord ++ tailWord_3101197).sum := by decide
  have hdescent : baseEnd_3101197 < baseStart_3101197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101253 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_3101253 : Nat := 118140960795 + 3101253 * 2 ^ 59
def prefixEnd_3101253 : Nat := 4983230072969 + 3 ^ 40 * 3101253 * 2
def baseEnd_3101253 : Nat := 1592433420198060067075103

theorem tailTrace_3101253 : CollatzResearch.WordTrace tailWord_3101253 prefixEnd_3101253 1592433420198060067075103 := by
  unfold tailWord_3101253
  simp only [CollatzResearch.WordTrace]
  refine ⟨113111989433697507689772413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75407992955798338459848275 113111989433697507689772413)
  ·
    refine ⟨42416996037636565383664655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113111989433697507689772413 42416996037636565383664655)
    ·
      refine ⟨63625494056454848075496983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42416996037636565383664655 63625494056454848075496983)
      ·
        refine ⟨95438241084682272113245475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63625494056454848075496983 95438241084682272113245475)
        ·
          refine ⟨143157361627023408169868213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95438241084682272113245475 143157361627023408169868213)
          ·
            refine ⟨13421002652533444515925145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143157361627023408169868213 13421002652533444515925145)
            ·
              refine ⟨10065751989400083386943859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13421002652533444515925145 10065751989400083386943859)
              ·
                refine ⟨15098627984100125080415789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10065751989400083386943859 15098627984100125080415789)
                ·
                  refine ⟨5661985494037546905155921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15098627984100125080415789 5661985494037546905155921)
                  ·
                    refine ⟨4246489120528160178866941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661985494037546905155921 4246489120528160178866941)
                    ·
                      refine ⟨1592433420198060067075103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246489120528160178866941 1592433420198060067075103)
                      ·
                        rfl

theorem cell23_3101253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_3101253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101253 prefixEnd_3101253 := by exact prefixLift 3101253
  have htrace : WordTrace (prefixWord ++ tailWord_3101253) baseStart_3101253 baseEnd_3101253 := by
    simpa [prefixWord, tailWord_3101253, baseEnd_3101253] using wordTrace_append hprefix tailTrace_3101253
  have hstable : (prefixWord ++ tailWord_3101253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101253).length < 2 ^ (prefixWord ++ tailWord_3101253).sum := by decide
  have hdescent : baseEnd_3101253 < baseStart_3101253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101254 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3101254 : Nat := 118140960795 + 3101254 * 2 ^ 59
def prefixEnd_3101254 : Nat := 4983230072969 + 3 ^ 40 * 3101254 * 2
def baseEnd_3101254 : Nat := 1592433933678714563162599

theorem tailTrace_3101254 : CollatzResearch.WordTrace tailWord_3101254 prefixEnd_3101254 1592433933678714563162599 := by
  unfold tailWord_3101254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534750809584183901892463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75408017271129256573705877 3534750809584183901892463)
  ·
    refine ⟨5302126214376275852838695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3534750809584183901892463 5302126214376275852838695)
    ·
      refine ⟨7953189321564413779258043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5302126214376275852838695 7953189321564413779258043)
      ·
        refine ⟨11929783982346620668887065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953189321564413779258043 11929783982346620668887065)
        ·
          refine ⟨8947337986759965501665299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11929783982346620668887065 8947337986759965501665299)
          ·
            refine ⟨13421006980139948252497949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8947337986759965501665299 13421006980139948252497949)
            ·
              refine ⟨5032877617552480594686731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13421006980139948252497949 5032877617552480594686731)
              ·
                refine ⟨7549316426328720892030097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032877617552480594686731 7549316426328720892030097)
                ·
                  refine ⟨5661987319746540669022573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549316426328720892030097 5661987319746540669022573)
                  ·
                    refine ⟨2123245244904952750883465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5661987319746540669022573 2123245244904952750883465)
                    ·
                      refine ⟨1592433933678714563162599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123245244904952750883465 1592433933678714563162599)
                      ·
                        rfl

theorem cell23_3101254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3101254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101254 prefixEnd_3101254 := by exact prefixLift 3101254
  have htrace : WordTrace (prefixWord ++ tailWord_3101254) baseStart_3101254 baseEnd_3101254 := by
    simpa [prefixWord, tailWord_3101254, baseEnd_3101254] using wordTrace_append hprefix tailTrace_3101254
  have hstable : (prefixWord ++ tailWord_3101254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101254).length < 2 ^ (prefixWord ++ tailWord_3101254).sum := by decide
  have hdescent : baseEnd_3101254 < baseStart_3101254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101306 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_3101306 : Nat := 118140960795 + 3101306 * 2 ^ 59
def prefixEnd_3101306 : Nat := 4983230072969 + 3 ^ 40 * 3101306 * 2
def baseEnd_3101306 : Nat := 1592460634672748359712359

theorem tailTrace_3101306 : CollatzResearch.WordTrace tailWord_3101306 prefixEnd_3101306 1592460634672748359712359 := by
  unfold tailWord_3101306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278480625626374435362943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75409281668336998494301181 28278480625626374435362943)
  ·
    refine ⟨42417720938439561653044415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28278480625626374435362943 42417720938439561653044415)
    ·
      refine ⟨63626581407659342479566623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42417720938439561653044415 63626581407659342479566623)
      ·
        refine ⟨95439872111489013719349935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63626581407659342479566623 95439872111489013719349935)
        ·
          refine ⟨143159808167233520579024903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95439872111489013719349935 143159808167233520579024903)
          ·
            refine ⟨214739712250850280868537355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143159808167233520579024903 214739712250850280868537355)
            ·
              refine ⟨322109568376275421302806033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214739712250850280868537355 322109568376275421302806033)
              ·
                refine ⟨241582176282206565977104525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322109568376275421302806033 241582176282206565977104525)
                ·
                  refine ⟨90593316105827462241414197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241582176282206565977104525 90593316105827462241414197)
                  ·
                    refine ⟨8493123384921324585132581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90593316105827462241414197 8493123384921324585132581)
                    ·
                      refine ⟨1592460634672748359712359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8493123384921324585132581 1592460634672748359712359)
                      ·
                        rfl

theorem cell23_3101306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_3101306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101306 prefixEnd_3101306 := by exact prefixLift 3101306
  have htrace : WordTrace (prefixWord ++ tailWord_3101306) baseStart_3101306 baseEnd_3101306 := by
    simpa [prefixWord, tailWord_3101306, baseEnd_3101306] using wordTrace_append hprefix tailTrace_3101306
  have hstable : (prefixWord ++ tailWord_3101306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101306).length < 2 ^ (prefixWord ++ tailWord_3101306).sum := by decide
  have hdescent : baseEnd_3101306 < baseStart_3101306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101361 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3101361 : Nat := 118140960795 + 3101361 * 2 ^ 59
def prefixEnd_3101361 : Nat := 4983230072969 + 3 ^ 40 * 3101361 * 2
def baseEnd_3101361 : Nat := 1592488876108745644524607

theorem tailTrace_3101361 : CollatzResearch.WordTrace tailWord_3101361 prefixEnd_3101361 1592488876108745644524607 := by
  unfold tailWord_3101361
  simp only [CollatzResearch.WordTrace]
  refine ⟨113115928517306242134703937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75410619011537494756469291 113115928517306242134703937)
  ·
    refine ⟨84836946387979681601027953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113115928517306242134703937 84836946387979681601027953)
    ·
      refine ⟨63627709790984761200770965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84836946387979681601027953 63627709790984761200770965)
      ·
        refine ⟨2982548896452410681286139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63627709790984761200770965 2982548896452410681286139)
        ·
          refine ⟨4473823344678616021929209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982548896452410681286139 4473823344678616021929209)
          ·
            refine ⟨3355367508508962016446907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4473823344678616021929209 3355367508508962016446907)
            ·
              refine ⟨5033051262763443024670361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355367508508962016446907 5033051262763443024670361)
              ·
                refine ⟨3774788447072582268502771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5033051262763443024670361 3774788447072582268502771)
                ·
                  refine ⟨5662182670608873402754157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774788447072582268502771 5662182670608873402754157)
                  ·
                    refine ⟨2123318501478327526032809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5662182670608873402754157 2123318501478327526032809)
                    ·
                      refine ⟨1592488876108745644524607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123318501478327526032809 1592488876108745644524607)
                      ·
                        rfl

theorem cell23_3101361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3101361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101361 prefixEnd_3101361 := by exact prefixLift 3101361
  have htrace : WordTrace (prefixWord ++ tailWord_3101361) baseStart_3101361 baseEnd_3101361 := by
    simpa [prefixWord, tailWord_3101361, baseEnd_3101361] using wordTrace_append hprefix tailTrace_3101361
  have hstable : (prefixWord ++ tailWord_3101361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101361).length < 2 ^ (prefixWord ++ tailWord_3101361).sum := by decide
  have hdescent : baseEnd_3101361 < baseStart_3101361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101393 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_3101393 : Nat := 118140960795 + 3101393 * 2 ^ 59
def prefixEnd_3101393 : Nat := 4983230072969 + 3 ^ 40 * 3101393 * 2
def baseEnd_3101393 : Nat := 530835102496563173108153

theorem tailTrace_3101393 : CollatzResearch.WordTrace tailWord_3101393 prefixEnd_3101393 530835102496563173108153 := by
  unfold tailWord_3101393
  simp only [CollatzResearch.WordTrace]
  refine ⟨113117095653190311599868833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75411397102126874399912555 113117095653190311599868833)
  ·
    refine ⟨84837821739892733699901625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113117095653190311599868833 84837821739892733699901625)
    ·
      refine ⟨63628366304919550274926219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84837821739892733699901625 63628366304919550274926219)
      ·
        refine ⟨95442549457379325412389329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63628366304919550274926219 95442549457379325412389329)
        ·
          refine ⟨71581912093034494059291997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95442549457379325412389329 71581912093034494059291997)
          ·
            refine ⟨26843217034887935272234499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71581912093034494059291997 26843217034887935272234499)
            ·
              refine ⟨40264825552331902908351749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26843217034887935272234499 40264825552331902908351749)
              ·
                refine ⟨7549654791062231795315953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40264825552331902908351749 7549654791062231795315953)
                ·
                  refine ⟨5662241093296673846486965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549654791062231795315953 5662241093296673846486965)
                  ·
                    refine ⟨530835102496563173108153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5662241093296673846486965 530835102496563173108153)
                    ·
                      rfl

theorem cell23_3101393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_3101393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101393 prefixEnd_3101393 := by exact prefixLift 3101393
  have htrace : WordTrace (prefixWord ++ tailWord_3101393) baseStart_3101393 baseEnd_3101393 := by
    simpa [prefixWord, tailWord_3101393, baseEnd_3101393] using wordTrace_append hprefix tailTrace_3101393
  have hstable : (prefixWord ++ tailWord_3101393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101393).length < 2 ^ (prefixWord ++ tailWord_3101393).sum := by decide
  have hdescent : baseEnd_3101393 < baseStart_3101393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101400 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 2, 5, 2]
def baseStart_3101400 : Nat := 118140960795 + 3101400 * 2 ^ 59
def prefixEnd_3101400 : Nat := 4983230072969 + 3 ^ 40 * 3101400 * 2
def baseEnd_3101400 : Nat := 1592508901854270991936927

theorem tailTrace_3101400 : CollatzResearch.WordTrace tailWord_3101400 prefixEnd_3101400 1592508901854270991936927 := by
  unfold tailWord_3101400
  simp only [CollatzResearch.WordTrace]
  refine ⟨56558675482082475897686827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75411567309443301196915769 56558675482082475897686827)
  ·
    refine ⟨84838013223123713846530241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56558675482082475897686827 84838013223123713846530241)
    ·
      refine ⟨63628509917342785384897681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84838013223123713846530241 63628509917342785384897681)
      ·
        refine ⟨47721382438007089038673261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63628509917342785384897681 47721382438007089038673261)
        ·
          refine ⟨17895518414252658389502473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47721382438007089038673261 17895518414252658389502473)
          ·
            refine ⟨13421638810689493792126855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17895518414252658389502473 13421638810689493792126855)
            ·
              refine ⟨20132458216034240688190283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13421638810689493792126855 20132458216034240688190283)
              ·
                refine ⟨30198687324051361032285425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20132458216034240688190283 30198687324051361032285425)
                ·
                  refine ⟨22649015493038520774214069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30198687324051361032285425 22649015493038520774214069)
                  ·
                    refine ⟨2123345202472361322582569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22649015493038520774214069 2123345202472361322582569)
                    ·
                      refine ⟨1592508901854270991936927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123345202472361322582569 1592508901854270991936927)
                      ·
                        rfl

theorem cell23_3101400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_3101400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101400 prefixEnd_3101400 := by exact prefixLift 3101400
  have htrace : WordTrace (prefixWord ++ tailWord_3101400) baseStart_3101400 baseEnd_3101400 := by
    simpa [prefixWord, tailWord_3101400, baseEnd_3101400] using wordTrace_append hprefix tailTrace_3101400
  have hstable : (prefixWord ++ tailWord_3101400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101400).length < 2 ^ (prefixWord ++ tailWord_3101400).sum := by decide
  have hdescent : baseEnd_3101400 < baseStart_3101400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101430 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3101430 : Nat := 118140960795 + 3101430 * 2 ^ 59
def prefixEnd_3101430 : Nat := 4983230072969 + 3 ^ 40 * 3101430 * 2
def baseEnd_3101430 : Nat := 1592524306273905874561789

theorem tailTrace_3101430 : CollatzResearch.WordTrace tailWord_3101430 prefixEnd_3101430 1592524306273905874561789 := by
  unfold tailWord_3101430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069902822128516682435359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75412296769370844612643829 7069902822128516682435359)
  ·
    refine ⟨10604854233192775023653039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7069902822128516682435359 10604854233192775023653039)
    ·
      refine ⟨15907281349789162535479559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10604854233192775023653039 15907281349789162535479559)
      ·
        refine ⟨23860922024683743803219339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15907281349789162535479559 23860922024683743803219339)
        ·
          refine ⟨35791383037025615704829009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23860922024683743803219339 35791383037025615704829009)
          ·
            refine ⟨26843537277769211778621757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35791383037025615704829009 26843537277769211778621757)
            ·
              refine ⟨10066326479163454416983159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26843537277769211778621757 10066326479163454416983159)
              ·
                refine ⟨15099489718745181625474739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10066326479163454416983159 15099489718745181625474739)
                ·
                  refine ⟨22649234578117772438212109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15099489718745181625474739 22649234578117772438212109)
                  ·
                    refine ⟨8493462966794164664329541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22649234578117772438212109 8493462966794164664329541)
                    ·
                      refine ⟨1592524306273905874561789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8493462966794164664329541 1592524306273905874561789)
                      ·
                        rfl

theorem cell23_3101430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3101430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101430 prefixEnd_3101430 := by exact prefixLift 3101430
  have htrace : WordTrace (prefixWord ++ tailWord_3101430) baseStart_3101430 baseEnd_3101430 := by
    simpa [prefixWord, tailWord_3101430, baseEnd_3101430] using wordTrace_append hprefix tailTrace_3101430
  have hstable : (prefixWord ++ tailWord_3101430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101430).length < 2 ^ (prefixWord ++ tailWord_3101430).sum := by decide
  have hdescent : baseEnd_3101430 < baseStart_3101430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101447 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3101447 : Nat := 118140960795 + 3101447 * 2 ^ 59
def prefixEnd_3101447 : Nat := 4983230072969 + 3 ^ 40 * 3101447 * 2
def baseEnd_3101447 : Nat := 1592533035445032308049211

theorem tailTrace_3101447 : CollatzResearch.WordTrace tailWord_3101447 prefixEnd_3101447 1592533035445032308049211 := by
  unfold tailWord_3101447
  simp only [CollatzResearch.WordTrace]
  refine ⟨113119065194994678822334595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75412710129996452548223063 113119065194994678822334595)
  ·
    refine ⟨169678597792492018233501893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113119065194994678822334595 169678597792492018233501893)
    ·
      refine ⟨31814737086092253418781605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169678597792492018233501893 31814737086092253418781605)
      ·
        refine ⟨5965263203642297516021551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31814737086092253418781605 5965263203642297516021551)
        ·
          refine ⟨8947894805463446274032327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965263203642297516021551 8947894805463446274032327)
          ·
            refine ⟨13421842208195169411048491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8947894805463446274032327 13421842208195169411048491)
            ·
              refine ⟨20132763312292754116572737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13421842208195169411048491 20132763312292754116572737)
              ·
                refine ⟨15099572484219565587429553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20132763312292754116572737 15099572484219565587429553)
                ·
                  refine ⟨11324679363164674190572165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15099572484219565587429553 11324679363164674190572165)
                  ·
                    refine ⟨2123377380593376410732281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11324679363164674190572165 2123377380593376410732281)
                    ·
                      refine ⟨1592533035445032308049211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123377380593376410732281 1592533035445032308049211)
                      ·
                        rfl

theorem cell23_3101447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3101447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101447 prefixEnd_3101447 := by exact prefixLift 3101447
  have htrace : WordTrace (prefixWord ++ tailWord_3101447) baseStart_3101447 baseEnd_3101447 := by
    simpa [prefixWord, tailWord_3101447, baseEnd_3101447] using wordTrace_append hprefix tailTrace_3101447
  have hstable : (prefixWord ++ tailWord_3101447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101447).length < 2 ^ (prefixWord ++ tailWord_3101447).sum := by decide
  have hdescent : baseEnd_3101447 < baseStart_3101447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101450 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3101450 : Nat := 118140960795 + 3101450 * 2 ^ 59
def prefixEnd_3101450 : Nat := 4983230072969 + 3 ^ 40 * 3101450 * 2
def baseEnd_3101450 : Nat := 1592534575886995796311697

theorem tailTrace_3101450 : CollatzResearch.WordTrace tailWord_3101450 prefixEnd_3101450 1592534575886995796311697 := by
  unfold tailWord_3101450
  simp only [CollatzResearch.WordTrace]
  refine ⟨28279793653495952583673451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75412783075989206889795869 28279793653495952583673451)
  ·
    refine ⟨42419690480243928875510177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28279793653495952583673451 42419690480243928875510177)
    ·
      refine ⟨31814767860182946656632633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42419690480243928875510177 31814767860182946656632633)
      ·
        refine ⟨23861075895137209992474475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31814767860182946656632633 23861075895137209992474475)
        ·
          refine ⟨35791613842705814988711713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23861075895137209992474475 35791613842705814988711713)
          ·
            refine ⟨26843710382029361241533785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35791613842705814988711713 26843710382029361241533785)
            ·
              refine ⟨20132782786522020931150339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26843710382029361241533785 20132782786522020931150339)
              ·
                refine ⟨30199174179783031396725509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20132782786522020931150339 30199174179783031396725509)
                ·
                  refine ⟨5662345158709318386886033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30199174179783031396725509 5662345158709318386886033)
                  ·
                    refine ⟨4246758869031988790164525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5662345158709318386886033 4246758869031988790164525)
                    ·
                      refine ⟨1592534575886995796311697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246758869031988790164525 1592534575886995796311697)
                      ·
                        rfl

theorem cell23_3101450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3101450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101450 prefixEnd_3101450 := by exact prefixLift 3101450
  have htrace : WordTrace (prefixWord ++ tailWord_3101450) baseStart_3101450 baseEnd_3101450 := by
    simpa [prefixWord, tailWord_3101450, baseEnd_3101450] using wordTrace_append hprefix tailTrace_3101450
  have hstable : (prefixWord ++ tailWord_3101450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101450).length < 2 ^ (prefixWord ++ tailWord_3101450).sum := by decide
  have hdescent : baseEnd_3101450 < baseStart_3101450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101457 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 1, 4]
def baseStart_3101457 : Nat := 118140960795 + 3101457 * 2 ^ 59
def prefixEnd_3101457 : Nat := 4983230072969 + 3 ^ 40 * 3101457 * 2
def baseEnd_3101457 : Nat := 530846056750525756308055

theorem tailTrace_3101457 : CollatzResearch.WordTrace tailWord_3101457 prefixEnd_3101457 530846056750525756308055 := by
  unfold tailWord_3101457
  simp only [CollatzResearch.WordTrace]
  refine ⟨113119429924958450530198625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75412953283305633686799083 113119429924958450530198625)
  ·
    refine ⟨84839572443718837897648969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113119429924958450530198625 84839572443718837897648969)
    ·
      refine ⟨63629679332789128423236727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84839572443718837897648969 63629679332789128423236727)
      ·
        refine ⟨95444518999183692634855091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63629679332789128423236727 95444518999183692634855091)
        ·
          refine ⟨143166778498775538952282637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95444518999183692634855091 143166778498775538952282637)
          ·
            refine ⟨53687541937040827107105989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143166778498775538952282637 53687541937040827107105989)
            ·
              refine ⟨10066414113195155082582373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53687541937040827107105989 10066414113195155082582373)
              ·
                refine ⟨1887452646224091577984195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10066414113195155082582373 1887452646224091577984195)
                ·
                  refine ⟨2831178969336137366976293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887452646224091577984195 2831178969336137366976293)
                  ·
                    refine ⟨530846056750525756308055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831178969336137366976293 530846056750525756308055)
                    ·
                      rfl

theorem cell23_3101457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_3101457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101457 prefixEnd_3101457 := by exact prefixLift 3101457
  have htrace : WordTrace (prefixWord ++ tailWord_3101457) baseStart_3101457 baseEnd_3101457 := by
    simpa [prefixWord, tailWord_3101457, baseEnd_3101457] using wordTrace_append hprefix tailTrace_3101457
  have hstable : (prefixWord ++ tailWord_3101457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101457).length < 2 ^ (prefixWord ++ tailWord_3101457).sum := by decide
  have hdescent : baseEnd_3101457 < baseStart_3101457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101473 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3101473 : Nat := 118140960795 + 3101473 * 2 ^ 59
def prefixEnd_3101473 : Nat := 4983230072969 + 3 ^ 40 * 3101473 * 2
def baseEnd_3101473 : Nat := 1592546385942049206324091

theorem tailTrace_3101473 : CollatzResearch.WordTrace tailWord_3101473 prefixEnd_3101473 1592546385942049206324091 := by
  unfold tailWord_3101473
  simp only [CollatzResearch.WordTrace]
  refine ⟨113120013492900485262781073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75413342328600323508520715 113120013492900485262781073)
  ·
    refine ⟨84840010119675363947085805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113120013492900485262781073 84840010119675363947085805)
    ·
      refine ⟨31815003794878261480157177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84840010119675363947085805 31815003794878261480157177)
      ·
        refine ⟨23861252846158696110117883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31815003794878261480157177 23861252846158696110117883)
        ·
          refine ⟨35791879269238044165176825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23861252846158696110117883 35791879269238044165176825)
          ·
            refine ⟨26843909451928533123882619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35791879269238044165176825 26843909451928533123882619)
            ·
              refine ⟨40265864177892799685823929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26843909451928533123882619 40265864177892799685823929)
              ·
                refine ⟨30199398133419599764367947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40265864177892799685823929 30199398133419599764367947)
                ·
                  refine ⟨45299097200129399646551921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30199398133419599764367947 45299097200129399646551921)
                  ·
                    refine ⟨33974322900097049734913941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45299097200129399646551921 33974322900097049734913941)
                    ·
                      refine ⟨1592546385942049206324091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33974322900097049734913941 1592546385942049206324091)
                      ·
                        rfl

theorem cell23_3101473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3101473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101473 prefixEnd_3101473 := by exact prefixLift 3101473
  have htrace : WordTrace (prefixWord ++ tailWord_3101473) baseStart_3101473 baseEnd_3101473 := by
    simpa [prefixWord, tailWord_3101473, baseEnd_3101473] using wordTrace_append hprefix tailTrace_3101473
  have hstable : (prefixWord ++ tailWord_3101473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101473).length < 2 ^ (prefixWord ++ tailWord_3101473).sum := by decide
  have hdescent : baseEnd_3101473 < baseStart_3101473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101480 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3101480 : Nat := 118140960795 + 3101480 * 2 ^ 59
def prefixEnd_3101480 : Nat := 4983230072969 + 3 ^ 40 * 3101480 * 2
def baseEnd_3101480 : Nat := 1592549980306630678936559

theorem tailTrace_3101480 : CollatzResearch.WordTrace tailWord_3101480 prefixEnd_3101480 1592549980306630678936559 := by
  unfold tailWord_3101480
  simp only [CollatzResearch.WordTrace]
  refine ⟨56560134401937562729142947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75413512535916750305523929 56560134401937562729142947)
  ·
    refine ⟨84840201602906344093714421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56560134401937562729142947 84840201602906344093714421)
    ·
      refine ⟨7953768900272469758785727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84840201602906344093714421 7953768900272469758785727)
      ·
        refine ⟨11930653350408704638178591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953768900272469758785727 11930653350408704638178591)
        ·
          refine ⟨17895980025613056957267887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11930653350408704638178591 17895980025613056957267887)
          ·
            refine ⟨26843970038419585435901831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17895980025613056957267887 26843970038419585435901831)
            ·
              refine ⟨40265955057629378153852747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26843970038419585435901831 40265955057629378153852747)
              ·
                refine ⟨60398932586444067230779121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40265955057629378153852747 60398932586444067230779121)
                ·
                  refine ⟨45299199439833050423084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60398932586444067230779121 45299199439833050423084341)
                  ·
                    refine ⟨4246799947484348477164157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45299199439833050423084341 4246799947484348477164157)
                    ·
                      refine ⟨1592549980306630678936559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4246799947484348477164157 1592549980306630678936559)
                      ·
                        rfl

theorem cell23_3101480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3101480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101480 prefixEnd_3101480 := by exact prefixLift 3101480
  have htrace : WordTrace (prefixWord ++ tailWord_3101480) baseStart_3101480 baseEnd_3101480 := by
    simpa [prefixWord, tailWord_3101480, baseEnd_3101480] using wordTrace_append hprefix tailTrace_3101480
  have hstable : (prefixWord ++ tailWord_3101480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101480).length < 2 ^ (prefixWord ++ tailWord_3101480).sum := by decide
  have hdescent : baseEnd_3101480 < baseStart_3101480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101507 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 2, 3, 2]
def baseStart_3101507 : Nat := 118140960795 + 3101507 * 2 ^ 59
def prefixEnd_3101507 : Nat := 4983230072969 + 3 ^ 40 * 3101507 * 2
def baseEnd_3101507 : Nat := 1592563844284302073298935

theorem tailTrace_3101507 : CollatzResearch.WordTrace tailWord_3101507 prefixEnd_3101507 1592563844284302073298935 := by
  unfold tailWord_3101507
  simp only [CollatzResearch.WordTrace]
  refine ⟨113121253574777309069518775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75414169049851539379679183 113121253574777309069518775)
  ·
    refine ⟨169681880362165963604278163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113121253574777309069518775 169681880362165963604278163)
    ·
      refine ⟨254522820543248945406417245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169681880362165963604278163 254522820543248945406417245)
      ·
        refine ⟨95446057703718354527406467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254522820543248945406417245 95446057703718354527406467)
        ·
          refine ⟨143169086555577531791109701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95446057703718354527406467 143169086555577531791109701)
          ·
            refine ⟨26844203729170787210833069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143169086555577531791109701 26844203729170787210833069)
            ·
              refine ⟨10066576398439045204062401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26844203729170787210833069 10066576398439045204062401)
              ·
                refine ⟨7549932298829283903046801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10066576398439045204062401 7549932298829283903046801)
                ·
                  refine ⟨5662449224121962927285101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549932298829283903046801 5662449224121962927285101)
                  ·
                    refine ⟨2123418459045736097731913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5662449224121962927285101 2123418459045736097731913)
                    ·
                      refine ⟨1592563844284302073298935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123418459045736097731913 1592563844284302073298935)
                      ·
                        rfl

theorem cell23_3101507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_3101507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101507 prefixEnd_3101507 := by exact prefixLift 3101507
  have htrace : WordTrace (prefixWord ++ tailWord_3101507) baseStart_3101507 baseEnd_3101507 := by
    simpa [prefixWord, tailWord_3101507, baseEnd_3101507] using wordTrace_append hprefix tailTrace_3101507
  have hstable : (prefixWord ++ tailWord_3101507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101507).length < 2 ^ (prefixWord ++ tailWord_3101507).sum := by decide
  have hdescent : baseEnd_3101507 < baseStart_3101507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101508 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3101508 : Nat := 118140960795 + 3101508 * 2 ^ 59
def prefixEnd_3101508 : Nat := 4983230072969 + 3 ^ 40 * 3101508 * 2
def baseEnd_3101508 : Nat := 530854785921652189795477

theorem tailTrace_3101508 : CollatzResearch.WordTrace tailWord_3101508 prefixEnd_3101508 530854785921652189795477 := by
  unfold tailWord_3101508
  simp only [CollatzResearch.WordTrace]
  refine ⟨56560645023886843120152589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75414193365182457493536785 56560645023886843120152589)
  ·
    refine ⟨21210241883957566170057221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56560645023886843120152589 21210241883957566170057221)
    ·
      refine ⟨3976920353242043656885729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21210241883957566170057221 3976920353242043656885729)
      ·
        refine ⟨2982690264931532742664297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3976920353242043656885729 2982690264931532742664297)
        ·
          refine ⟨2237017698698649556998223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982690264931532742664297 2237017698698649556998223)
          ·
            refine ⟨3355526548047974335497335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237017698698649556998223 3355526548047974335497335)
            ·
              refine ⟨5033289822071961503246003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355526548047974335497335 5033289822071961503246003)
              ·
                refine ⟨7549934733107942254869005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033289822071961503246003 7549934733107942254869005)
                ·
                  refine ⟨2831225524915478345575877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7549934733107942254869005 2831225524915478345575877)
                  ·
                    refine ⟨530854785921652189795477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831225524915478345575877 530854785921652189795477)
                    ·
                      rfl

theorem cell23_3101508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3101508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101508 prefixEnd_3101508 := by exact prefixLift 3101508
  have htrace : WordTrace (prefixWord ++ tailWord_3101508) baseStart_3101508 baseEnd_3101508 := by
    simpa [prefixWord, tailWord_3101508, baseEnd_3101508] using wordTrace_append hprefix tailTrace_3101508
  have hstable : (prefixWord ++ tailWord_3101508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101508).length < 2 ^ (prefixWord ++ tailWord_3101508).sum := by decide
  have hdescent : baseEnd_3101508 < baseStart_3101508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101557 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3101557 : Nat := 118140960795 + 3101557 * 2 ^ 59
def prefixEnd_3101557 : Nat := 4983230072969 + 3 ^ 40 * 3101557 * 2
def baseEnd_3101557 : Nat := 1592589518317026877673705

theorem tailTrace_3101557 : CollatzResearch.WordTrace tailWord_3101557 prefixEnd_3101557 1592589518317026877673705 := by
  unfold tailWord_3101557
  simp only [CollatzResearch.WordTrace]
  refine ⟨113123077224596167608838925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75415384816397445072559283 113123077224596167608838925)
  ·
    refine ⟨42421153959223562853314597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113123077224596167608838925 42421153959223562853314597)
    ·
      refine ⟨7953966367354418034996487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42421153959223562853314597 7953966367354418034996487)
      ·
        refine ⟨11930949551031627052494731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953966367354418034996487 11930949551031627052494731)
        ·
          refine ⟨17896424326547440578742097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11930949551031627052494731 17896424326547440578742097)
          ·
            refine ⟨13422318244910580434056573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17896424326547440578742097 13422318244910580434056573)
            ·
              refine ⟨5033369341841467662771215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13422318244910580434056573 5033369341841467662771215)
              ·
                refine ⟨7550054012762201494156823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033369341841467662771215 7550054012762201494156823)
                ·
                  refine ⟨11325081019143302241235235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550054012762201494156823 11325081019143302241235235)
                  ·
                    refine ⟨16987621528714953361852853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11325081019143302241235235 16987621528714953361852853)
                    ·
                      refine ⟨1592589518317026877673705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16987621528714953361852853 1592589518317026877673705)
                      ·
                        rfl

theorem cell23_3101557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3101557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101557 prefixEnd_3101557 := by exact prefixLift 3101557
  have htrace : WordTrace (prefixWord ++ tailWord_3101557) baseStart_3101557 baseEnd_3101557 := by
    simpa [prefixWord, tailWord_3101557, baseEnd_3101557] using wordTrace_append hprefix tailTrace_3101557
  have hstable : (prefixWord ++ tailWord_3101557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101557).length < 2 ^ (prefixWord ++ tailWord_3101557).sum := by decide
  have hdescent : baseEnd_3101557 < baseStart_3101557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101571 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 1, 2, 2]
def baseStart_3101571 : Nat := 118140960795 + 3101571 * 2 ^ 59
def prefixEnd_3101571 : Nat := 4983230072969 + 3 ^ 40 * 3101571 * 2
def baseEnd_3101571 : Nat := 1592596707046189822898641

theorem tailTrace_3101571 : CollatzResearch.WordTrace tailWord_3101571 prefixEnd_3101571 1592596707046189822898641 := by
  unfold tailWord_3101571
  simp only [CollatzResearch.WordTrace]
  refine ⟨113123587846545447999848567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75415725231030298666565711 113123587846545447999848567)
  ·
    refine ⟨169685381769818171999772851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113123587846545447999848567 169685381769818171999772851)
    ·
      refine ⟨254528072654727257999659277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169685381769818171999772851 254528072654727257999659277)
      ·
        refine ⟨95448027245522721749872229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254528072654727257999659277 95448027245522721749872229)
        ·
          refine ⟨17896505108535510328101043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95448027245522721749872229 17896505108535510328101043)
          ·
            refine ⟨26844757662803265492151565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17896505108535510328101043 26844757662803265492151565)
            ·
              refine ⟨10066784123551224559556837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26844757662803265492151565 10066784123551224559556837)
              ·
                refine ⟨1887522023165854604916907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10066784123551224559556837 1887522023165854604916907)
                ·
                  refine ⟨2831283034748781907375361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887522023165854604916907 2831283034748781907375361)
                  ·
                    refine ⟨2123462276061586430531521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831283034748781907375361 2123462276061586430531521)
                    ·
                      refine ⟨1592596707046189822898641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123462276061586430531521 1592596707046189822898641)
                      ·
                        rfl

theorem cell23_3101571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_3101571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101571 prefixEnd_3101571 := by exact prefixLift 3101571
  have htrace : WordTrace (prefixWord ++ tailWord_3101571) baseStart_3101571 baseEnd_3101571 := by
    simpa [prefixWord, tailWord_3101571, baseEnd_3101571] using wordTrace_append hprefix tailTrace_3101571
  have hstable : (prefixWord ++ tailWord_3101571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101571).length < 2 ^ (prefixWord ++ tailWord_3101571).sum := by decide
  have hdescent : baseEnd_3101571 < baseStart_3101571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101622 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3101622 : Nat := 118140960795 + 3101622 * 2 ^ 59
def prefixEnd_3101622 : Nat := 4983230072969 + 3 ^ 40 * 3101622 * 2
def baseEnd_3101622 : Nat := 1592622894559569123360907

theorem tailTrace_3101622 : CollatzResearch.WordTrace tailWord_3101622 prefixEnd_3101622 1592622894559569123360907 := by
  unfold tailWord_3101622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070340498085042731872195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75416965312907122473303413 7070340498085042731872195)
  ·
    refine ⟨10605510747127564097808293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070340498085042731872195 10605510747127564097808293)
    ·
      refine ⟨1988533265086418268339055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10605510747127564097808293 1988533265086418268339055)
      ·
        refine ⟨2982799897629627402508583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988533265086418268339055 2982799897629627402508583)
        ·
          refine ⟨4474199846444441103762875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982799897629627402508583 4474199846444441103762875)
          ·
            refine ⟨6711299769666661655644313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474199846444441103762875 6711299769666661655644313)
            ·
              refine ⟨5033474827249996241733235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6711299769666661655644313 5033474827249996241733235)
              ·
                refine ⟨7550212240874994362599853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033474827249996241733235 7550212240874994362599853)
                ·
                  refine ⟨2831329590328122885974945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7550212240874994362599853 2831329590328122885974945)
                  ·
                    refine ⟨2123497192746092164481209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831329590328122885974945 2123497192746092164481209)
                    ·
                      refine ⟨1592622894559569123360907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123497192746092164481209 1592622894559569123360907)
                      ·
                        rfl

theorem cell23_3101622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3101622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101622 prefixEnd_3101622 := by exact prefixLift 3101622
  have htrace : WordTrace (prefixWord ++ tailWord_3101622) baseStart_3101622 baseEnd_3101622 := by
    simpa [prefixWord, tailWord_3101622, baseEnd_3101622] using wordTrace_append hprefix tailTrace_3101622
  have hstable : (prefixWord ++ tailWord_3101622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101622).length < 2 ^ (prefixWord ++ tailWord_3101622).sum := by decide
  have hdescent : baseEnd_3101622 < baseStart_3101622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101645 : List Nat := [1, 6, 3, 1, 2, 1, 2, 7]
def baseStart_3101645 : Nat := 118140960795 + 3101645 * 2 ^ 59
def prefixEnd_3101645 : Nat := 4983230072969 + 3 ^ 40 * 3101645 * 2
def baseEnd_3101645 : Nat := 58986470541282316050863

theorem tailTrace_3101645 : CollatzResearch.WordTrace tailWord_3101645 prefixEnd_3101645 58986470541282316050863 := by
  unfold tailWord_3101645
  simp only [CollatzResearch.WordTrace]
  refine ⟨113126286848277358638042389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75417524565518239092028259 113126286848277358638042389)
  ·
    refine ⟨5302794696013001186158237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113126286848277358638042389 5302794696013001186158237)
    ·
      refine ⟨1988548011004875444809339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5302794696013001186158237 1988548011004875444809339)
      ·
        refine ⟨2982822016507313167214009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988548011004875444809339 2982822016507313167214009)
        ·
          refine ⟨2237116512380484875410507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982822016507313167214009 2237116512380484875410507)
          ·
            refine ⟨3355674768570727313115761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237116512380484875410507 3355674768570727313115761)
            ·
              refine ⟨2516756076428045484836821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355674768570727313115761 2516756076428045484836821)
              ·
                refine ⟨58986470541282316050863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2516756076428045484836821 58986470541282316050863)
                ·
                  rfl

theorem cell23_3101645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 7].length) (baseStart_3101645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101645 prefixEnd_3101645 := by exact prefixLift 3101645
  have htrace : WordTrace (prefixWord ++ tailWord_3101645) baseStart_3101645 baseEnd_3101645 := by
    simpa [prefixWord, tailWord_3101645, baseEnd_3101645] using wordTrace_append hprefix tailTrace_3101645
  have hstable : (prefixWord ++ tailWord_3101645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101645).length < 2 ^ (prefixWord ++ tailWord_3101645).sum := by decide
  have hdescent : baseEnd_3101645 < baseStart_3101645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101661 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_3101661 : Nat := 118140960795 + 3101661 * 2 ^ 59
def prefixEnd_3101661 : Nat := 4983230072969 + 3 ^ 40 * 3101661 * 2
def baseEnd_3101661 : Nat := 1592642920305094470773227

theorem tailTrace_3101661 : CollatzResearch.WordTrace tailWord_3101661 prefixEnd_3101661 1592642920305094470773227 := by
  unfold tailWord_3101661
  simp only [CollatzResearch.WordTrace]
  refine ⟨113126870416219393370624837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75417913610812928913749891 113126870416219393370624837)
  ·
    refine ⟨21211288203041136256992157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113126870416219393370624837 21211288203041136256992157)
    ·
      refine ⟨7954233076140426096372059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21211288203041136256992157 7954233076140426096372059)
      ·
        refine ⟨11931349614210639144558089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7954233076140426096372059 11931349614210639144558089)
        ·
          refine ⟨8948512210657979358418567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11931349614210639144558089 8948512210657979358418567)
          ·
            refine ⟨13422768315986969037627851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948512210657979358418567 13422768315986969037627851)
            ·
              refine ⟨20134152473980453556441777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13422768315986969037627851 20134152473980453556441777)
              ·
                refine ⟨15100614355485340167331333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20134152473980453556441777 15100614355485340167331333)
                ·
                  refine ⟨2831365191653501281374625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15100614355485340167331333 2831365191653501281374625)
                  ·
                    refine ⟨2123523893740125961030969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831365191653501281374625 2123523893740125961030969)
                    ·
                      refine ⟨1592642920305094470773227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123523893740125961030969 1592642920305094470773227)
                      ·
                        rfl

theorem cell23_3101661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_3101661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101661 prefixEnd_3101661 := by exact prefixLift 3101661
  have htrace : WordTrace (prefixWord ++ tailWord_3101661) baseStart_3101661 baseEnd_3101661 := by
    simpa [prefixWord, tailWord_3101661, baseEnd_3101661] using wordTrace_append hprefix tailTrace_3101661
  have hstable : (prefixWord ++ tailWord_3101661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101661).length < 2 ^ (prefixWord ++ tailWord_3101661).sum := by decide
  have hdescent : baseEnd_3101661 < baseStart_3101661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101761 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3101761 : Nat := 118140960795 + 3101761 * 2 ^ 59
def prefixEnd_3101761 : Nat := 4983230072969 + 3 ^ 40 * 3101761 * 2
def baseEnd_3101761 : Nat := 530898089456848026507589

theorem tailTrace_3101761 : CollatzResearch.WordTrace tailWord_3101761 prefixEnd_3101761 530898089456848026507589 := by
  unfold tailWord_3101761
  simp only [CollatzResearch.WordTrace]
  refine ⟨113130517715857110449265137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75420345143904740299510091 113130517715857110449265137)
  ·
    refine ⟨84847888286892832836948853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113130517715857110449265137 84847888286892832836948853)
    ·
      refine ⟨7954489526896203078463955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84847888286892832836948853 7954489526896203078463955)
      ·
        refine ⟨11931734290344304617695933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7954489526896203078463955 11931734290344304617695933)
        ·
          refine ⟨4474400358879114231635975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11931734290344304617695933 4474400358879114231635975)
          ·
            refine ⟨6711600538318671347453963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474400358879114231635975 6711600538318671347453963)
            ·
              refine ⟨10067400807478007021180945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6711600538318671347453963 10067400807478007021180945)
              ·
                refine ⟨7550550605608505265885709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10067400807478007021180945 7550550605608505265885709)
                ·
                  refine ⟨2831456477103189474707141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7550550605608505265885709 2831456477103189474707141)
                  ·
                    refine ⟨530898089456848026507589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831456477103189474707141 530898089456848026507589)
                    ·
                      rfl

theorem cell23_3101761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3101761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101761 prefixEnd_3101761 := by exact prefixLift 3101761
  have htrace : WordTrace (prefixWord ++ tailWord_3101761) baseStart_3101761 baseEnd_3101761 := by
    simpa [prefixWord, tailWord_3101761, baseEnd_3101761] using wordTrace_append hprefix tailTrace_3101761
  have hstable : (prefixWord ++ tailWord_3101761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101761).length < 2 ^ (prefixWord ++ tailWord_3101761).sum := by decide
  have hdescent : baseEnd_3101761 < baseStart_3101761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101778 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3101778 : Nat := 118140960795 + 3101778 * 2 ^ 59
def prefixEnd_3101778 : Nat := 4983230072969 + 3 ^ 40 * 3101778 * 2
def baseEnd_3101778 : Nat := 530900999180556837670063

theorem tailTrace_3101778 : CollatzResearch.WordTrace tailWord_3101778 prefixEnd_3101778 530900999180556837670063 := by
  unfold tailWord_3101778
  simp only [CollatzResearch.WordTrace]
  refine ⟨28282784439198880588158497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75420758504530348235089325 28282784439198880588158497)
  ·
    refine ⟨21212088329399160441118873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28282784439198880588158497 21212088329399160441118873)
    ·
      refine ⟨15909066247049370330839155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21212088329399160441118873 15909066247049370330839155)
      ·
        refine ⟨23863599370574055496258733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15909066247049370330839155 23863599370574055496258733)
        ·
          refine ⟨8948849763965270811097025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23863599370574055496258733 8948849763965270811097025)
          ·
            refine ⟨6711637322973953108322769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8948849763965270811097025 6711637322973953108322769)
            ·
              refine ⟨5033727992230464831242077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6711637322973953108322769 5033727992230464831242077)
              ·
                refine ⟨1887647997086424311715779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5033727992230464831242077 1887647997086424311715779)
                ·
                  refine ⟨2831471995629636467573669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887647997086424311715779 2831471995629636467573669)
                  ·
                    refine ⟨530900999180556837670063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831471995629636467573669 530900999180556837670063)
                    ·
                      rfl

theorem cell23_3101778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3101778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101778 prefixEnd_3101778 := by exact prefixLift 3101778
  have htrace : WordTrace (prefixWord ++ tailWord_3101778) baseStart_3101778 baseEnd_3101778 := by
    simpa [prefixWord, tailWord_3101778, baseEnd_3101778] using wordTrace_append hprefix tailTrace_3101778
  have hstable : (prefixWord ++ tailWord_3101778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101778).length < 2 ^ (prefixWord ++ tailWord_3101778).sum := by decide
  have hdescent : baseEnd_3101778 < baseStart_3101778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101784 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3101784 : Nat := 118140960795 + 3101784 * 2 ^ 59
def prefixEnd_3101784 : Nat := 4983230072969 + 3 ^ 40 * 3101784 * 2
def baseEnd_3101784 : Nat := 1592706078425597489535161

theorem tailTrace_3101784 : CollatzResearch.WordTrace tailWord_3101784 prefixEnd_3101784 1592706078425597489535161 := by
  unfold tailWord_3101784
  simp only [CollatzResearch.WordTrace]
  refine ⟨56565678297386892688676203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75420904396515856918234937 56565678297386892688676203)
  ·
    refine ⟨84848517446080339033014305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56565678297386892688676203 84848517446080339033014305)
    ·
      refine ⟨63636388084560254274760729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84848517446080339033014305 63636388084560254274760729)
      ·
        refine ⟨47727291063420190706070547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63636388084560254274760729 47727291063420190706070547)
        ·
          refine ⟨71590936595130286059105821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47727291063420190706070547 71590936595130286059105821)
          ·
            refine ⟨26846601223173857272164683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71590936595130286059105821 26846601223173857272164683)
            ·
              refine ⟨40269901834760785908247025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26846601223173857272164683 40269901834760785908247025)
              ·
                refine ⟨30202426376070589431185269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40269901834760785908247025 30202426376070589431185269)
                ·
                  refine ⟨2831477472756617759173619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30202426376070589431185269 2831477472756617759173619)
                  ·
                    refine ⟨4247216209134926638760429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2831477472756617759173619 4247216209134926638760429)
                    ·
                      refine ⟨1592706078425597489535161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4247216209134926638760429 1592706078425597489535161)
                      ·
                        rfl

theorem cell23_3101784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3101784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101784 prefixEnd_3101784 := by exact prefixLift 3101784
  have htrace : WordTrace (prefixWord ++ tailWord_3101784) baseStart_3101784 baseEnd_3101784 := by
    simpa [prefixWord, tailWord_3101784, baseEnd_3101784] using wordTrace_append hprefix tailTrace_3101784
  have hstable : (prefixWord ++ tailWord_3101784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101784).length < 2 ^ (prefixWord ++ tailWord_3101784).sum := by decide
  have hdescent : baseEnd_3101784 < baseStart_3101784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101794 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3101794 : Nat := 118140960795 + 3101794 * 2 ^ 59
def prefixEnd_3101794 : Nat := 4983230072969 + 3 ^ 40 * 3101794 * 2
def baseEnd_3101794 : Nat := 1592711213232142450410115

theorem tailTrace_3101794 : CollatzResearch.WordTrace tailWord_3101794 prefixEnd_3101794 1592711213232142450410115 := by
  unfold tailWord_3101794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28282930331184389271304109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75421147549825038056810957 28282930331184389271304109)
  ·
    refine ⟨10606098874194145976739041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28282930331184389271304109 10606098874194145976739041)
    ·
      refine ⟨7954574155645609482554281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10606098874194145976739041 7954574155645609482554281)
      ·
        refine ⟨5965930616734207111915711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7954574155645609482554281 5965930616734207111915711)
        ·
          refine ⟨8948895925101310667873567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965930616734207111915711 8948895925101310667873567)
          ·
            refine ⟨13423343887651966001810351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948895925101310667873567 13423343887651966001810351)
            ·
              refine ⟨20135015831477949002715527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13423343887651966001810351 20135015831477949002715527)
              ·
                refine ⟨30202523747216923504073291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20135015831477949002715527 30202523747216923504073291)
                ·
                  refine ⟨45303785620825385256109937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30202523747216923504073291 45303785620825385256109937)
                  ·
                    refine ⟨33977839215619038942082453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45303785620825385256109937 33977839215619038942082453)
                    ·
                      refine ⟨1592711213232142450410115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33977839215619038942082453 1592711213232142450410115)
                      ·
                        rfl

theorem cell23_3101794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3101794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101794 prefixEnd_3101794 := by exact prefixLift 3101794
  have htrace : WordTrace (prefixWord ++ tailWord_3101794) baseStart_3101794 baseEnd_3101794 := by
    simpa [prefixWord, tailWord_3101794, baseEnd_3101794] using wordTrace_append hprefix tailTrace_3101794
  have hstable : (prefixWord ++ tailWord_3101794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101794).length < 2 ^ (prefixWord ++ tailWord_3101794).sum := by decide
  have hdescent : baseEnd_3101794 < baseStart_3101794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101801 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 3]
def baseStart_3101801 : Nat := 118140960795 + 3101801 * 2 ^ 59
def prefixEnd_3101801 : Nat := 4983230072969 + 3 ^ 40 * 3101801 * 2
def baseEnd_3101801 : Nat := 1592714807596723923022583

theorem tailTrace_3101801 : CollatzResearch.WordTrace tailWord_3101801 prefixEnd_3101801 1592714807596723923022583 := by
  unfold tailWord_3101801
  simp only [CollatzResearch.WordTrace]
  refine ⟨113131976635712197280721257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75421317757141464853814171 113131976635712197280721257)
  ·
    refine ⟨84848982476784147960540943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113131976635712197280721257 84848982476784147960540943)
    ·
      refine ⟨127273473715176221940811415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84848982476784147960540943 127273473715176221940811415)
      ·
        refine ⟨190910210572764332911217123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127273473715176221940811415 190910210572764332911217123)
        ·
          refine ⟨286365315859146499366825685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190910210572764332911217123 286365315859146499366825685)
          ·
            refine ⟨6711687090448746078909977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 286365315859146499366825685 6711687090448746078909977)
            ·
              refine ⟨5033765317836559559182483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6711687090448746078909977 5033765317836559559182483)
              ·
                refine ⟨7550647976754839338773725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033765317836559559182483 7550647976754839338773725)
                ·
                  refine ⟨2831492991283064752040147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7550647976754839338773725 2831492991283064752040147)
                  ·
                    refine ⟨4247239486924597128060221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2831492991283064752040147 4247239486924597128060221)
                    ·
                      refine ⟨1592714807596723923022583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4247239486924597128060221 1592714807596723923022583)
                      ·
                        rfl

theorem cell23_3101801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_3101801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101801 prefixEnd_3101801 := by exact prefixLift 3101801
  have htrace : WordTrace (prefixWord ++ tailWord_3101801) baseStart_3101801 baseEnd_3101801 := by
    simpa [prefixWord, tailWord_3101801, baseEnd_3101801] using wordTrace_append hprefix tailTrace_3101801
  have hstable : (prefixWord ++ tailWord_3101801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101801).length < 2 ^ (prefixWord ++ tailWord_3101801).sum := by decide
  have hdescent : baseEnd_3101801 < baseStart_3101801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101824 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4]
def baseStart_3101824 : Nat := 118140960795 + 3101824 * 2 ^ 59
def prefixEnd_3101824 : Nat := 4983230072969 + 3 ^ 40 * 3101824 * 2
def baseEnd_3101824 : Nat := 1592726617651777333034977

theorem tailTrace_3101824 : CollatzResearch.WordTrace tailWord_3101824 prefixEnd_3101824 1592726617651777333034977 := by
  unfold tailWord_3101824
  simp only [CollatzResearch.WordTrace]
  refine ⟨56566407757314436104404263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75421877009752581472539017 56566407757314436104404263)
  ·
    refine ⟨84849611635971654156606395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56566407757314436104404263 84849611635971654156606395)
    ·
      refine ⟨127274417453957481234909593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84849611635971654156606395 127274417453957481234909593)
      ·
        refine ⟨95455813090468110926182195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127274417453957481234909593 95455813090468110926182195)
        ·
          refine ⟨143183719635702166389273293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95455813090468110926182195 143183719635702166389273293)
          ·
            refine ⟨53693894863388312395977485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143183719635702166389273293 53693894863388312395977485)
            ·
              refine ⟨20135210573770617148491557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53693894863388312395977485 20135210573770617148491557)
              ·
                refine ⟨3775351982581990715342167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20135210573770617148491557 3775351982581990715342167)
                ·
                  refine ⟨5663027973872986073013251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775351982581990715342167 5663027973872986073013251)
                  ·
                    refine ⟨8494541960809479109519877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5663027973872986073013251 8494541960809479109519877)
                    ·
                      refine ⟨1592726617651777333034977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8494541960809479109519877 1592726617651777333034977)
                      ·
                        rfl

theorem cell23_3101824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_3101824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101824 prefixEnd_3101824 := by exact prefixLift 3101824
  have htrace : WordTrace (prefixWord ++ tailWord_3101824) baseStart_3101824 baseEnd_3101824 := by
    simpa [prefixWord, tailWord_3101824, baseEnd_3101824] using wordTrace_append hprefix tailTrace_3101824
  have hstable : (prefixWord ++ tailWord_3101824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101824).length < 2 ^ (prefixWord ++ tailWord_3101824).sum := by decide
  have hdescent : baseEnd_3101824 < baseStart_3101824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101827 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5]
def baseStart_3101827 : Nat := 118140960795 + 3101827 * 2 ^ 59
def prefixEnd_3101827 : Nat := 4983230072969 + 3 ^ 40 * 3101827 * 2
def baseEnd_3101827 : Nat := 1592728158093740821297463

theorem tailTrace_3101827 : CollatzResearch.WordTrace tailWord_3101827 prefixEnd_3101827 1592728158093740821297463 := by
  unfold tailWord_3101827
  simp only [CollatzResearch.WordTrace]
  refine ⟨113132924933618003721167735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75421949955745335814111823 113132924933618003721167735)
  ·
    refine ⟨169699387400427005581751603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113132924933618003721167735 169699387400427005581751603)
    ·
      refine ⟨254549081100640508372627405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169699387400427005581751603 254549081100640508372627405)
      ·
        refine ⟨95455905412740190639735277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254549081100640508372627405 95455905412740190639735277)
        ·
          refine ⟨35795964529777571489900729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95455905412740190639735277 35795964529777571489900729)
          ·
            refine ⟨26846973397333178617425547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35795964529777571489900729 26846973397333178617425547)
            ·
              refine ⟨40270460095999767926138321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26846973397333178617425547 40270460095999767926138321)
              ·
                refine ⟨30202845071999825944603741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40270460095999767926138321 30202845071999825944603741)
                ·
                  refine ⟨11326066901999934729226403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30202845071999825944603741 11326066901999934729226403)
                  ·
                    refine ⟨16989100352999902093839605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11326066901999934729226403 16989100352999902093839605)
                    ·
                      refine ⟨1592728158093740821297463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16989100352999902093839605 1592728158093740821297463)
                      ·
                        rfl

theorem cell23_3101827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_3101827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101827 prefixEnd_3101827 := by exact prefixLift 3101827
  have htrace : WordTrace (prefixWord ++ tailWord_3101827) baseStart_3101827 baseEnd_3101827 := by
    simpa [prefixWord, tailWord_3101827, baseEnd_3101827] using wordTrace_append hprefix tailTrace_3101827
  have hstable : (prefixWord ++ tailWord_3101827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101827).length < 2 ^ (prefixWord ++ tailWord_3101827).sum := by decide
  have hdescent : baseEnd_3101827 < baseStart_3101827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101834 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3101834 : Nat := 118140960795 + 3101834 * 2 ^ 59
def prefixEnd_3101834 : Nat := 4983230072969 + 3 ^ 40 * 3101834 * 2
def baseEnd_3101834 : Nat := 530910584152774097969977

theorem tailTrace_3101834 : CollatzResearch.WordTrace tailWord_3101834 prefixEnd_3101834 530910584152774097969977 := by
  unfold tailWord_3101834
  simp only [CollatzResearch.WordTrace]
  refine ⟨28283295061148160979168139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75422120163061762611115037 28283295061148160979168139)
  ·
    refine ⟨42424942591722241468752209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28283295061148160979168139 42424942591722241468752209)
    ·
      refine ⟨31818706943791681101564157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42424942591722241468752209 31818706943791681101564157)
      ·
        refine ⟨11932015103921880413086559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31818706943791681101564157 11932015103921880413086559)
        ·
          refine ⟨17898022655882820619629839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11932015103921880413086559 17898022655882820619629839)
          ·
            refine ⟨26847033983824230929444759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17898022655882820619629839 26847033983824230929444759)
            ·
              refine ⟨40270550975736346394167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26847033983824230929444759 40270550975736346394167139)
              ·
                refine ⟨60405826463604519591250709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40270550975736346394167139 60405826463604519591250709)
                ·
                  refine ⟨2831523115481461855839877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60405826463604519591250709 2831523115481461855839877)
                  ·
                    refine ⟨530910584152774097969977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831523115481461855839877 530910584152774097969977)
                    ·
                      rfl

theorem cell23_3101834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3101834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101834 prefixEnd_3101834 := by exact prefixLift 3101834
  have htrace : WordTrace (prefixWord ++ tailWord_3101834) baseStart_3101834 baseEnd_3101834 := by
    simpa [prefixWord, tailWord_3101834, baseEnd_3101834] using wordTrace_append hprefix tailTrace_3101834
  have hstable : (prefixWord ++ tailWord_3101834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101834).length < 2 ^ (prefixWord ++ tailWord_3101834).sum := by decide
  have hdescent : baseEnd_3101834 < baseStart_3101834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101847 : List Nat := [1, 1, 3, 3, 3, 1, 11]
def baseStart_3101847 : Nat := 118140960795 + 3101847 * 2 ^ 59
def prefixEnd_3101847 : Nat := 4983230072969 + 3 ^ 40 * 3101847 * 2
def baseEnd_3101847 : Nat := 19663437379096675840091

theorem tailTrace_3101847 : CollatzResearch.WordTrace tailWord_3101847 prefixEnd_3101847 19663437379096675840091 := by
  unfold tailWord_3101847
  simp only [CollatzResearch.WordTrace]
  refine ⟨113133654393545547136895795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75422436262363698091263863 113133654393545547136895795)
  ·
    refine ⟨169700481590318320705343693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113133654393545547136895795 169700481590318320705343693)
    ·
      refine ⟨63637680596369370264503885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169700481590318320705343693 63637680596369370264503885)
      ·
        refine ⟨23864130223638513849188957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63637680596369370264503885 23864130223638513849188957)
        ·
          refine ⟨8949048833864442693445859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23864130223638513849188957 8949048833864442693445859)
          ·
            refine ⟨13423573250796664040168789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8949048833864442693445859 13423573250796664040168789)
            ·
              refine ⟨19663437379096675840091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13423573250796664040168789 19663437379096675840091)
              ·
                rfl

theorem cell23_3101847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 11].length) (baseStart_3101847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101847 prefixEnd_3101847 := by exact prefixLift 3101847
  have htrace : WordTrace (prefixWord ++ tailWord_3101847) baseStart_3101847 baseEnd_3101847 := by
    simpa [prefixWord, tailWord_3101847, baseEnd_3101847] using wordTrace_append hprefix tailTrace_3101847
  have hstable : (prefixWord ++ tailWord_3101847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101847).length < 2 ^ (prefixWord ++ tailWord_3101847).sum := by decide
  have hdescent : baseEnd_3101847 < baseStart_3101847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101887 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_3101887 : Nat := 118140960795 + 3101887 * 2 ^ 59
def prefixEnd_3101887 : Nat := 4983230072969 + 3 ^ 40 * 3101887 * 2
def baseEnd_3101887 : Nat := 1592758966933010586547187

theorem tailTrace_3101887 : CollatzResearch.WordTrace tailWord_3101887 prefixEnd_3101887 1592758966933010586547187 := by
  unfold tailWord_3101887
  simp only [CollatzResearch.WordTrace]
  refine ⟨113135113313400633968351915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75423408875600422645567943 113135113313400633968351915)
  ·
    refine ⟨169702669970100950952527873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113135113313400633968351915 169702669970100950952527873)
    ·
      refine ⟨127277002477575713214395905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169702669970100950952527873 127277002477575713214395905)
      ·
        refine ⟨95457751858181784910796929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127277002477575713214395905 95457751858181784910796929)
        ·
          refine ⟨71593313893636338683097697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95457751858181784910796929 71593313893636338683097697)
          ·
            refine ⟨53694985420227254012323273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71593313893636338683097697 53694985420227254012323273)
            ·
              refine ⟨40271239065170440509242455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53694985420227254012323273 40271239065170440509242455)
              ·
                refine ⟨60406858597755660763863683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40271239065170440509242455 60406858597755660763863683)
                ·
                  refine ⟨90610287896633491145795525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60406858597755660763863683 90610287896633491145795525)
                  ·
                    refine ⟨16989428980618779589836661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90610287896633491145795525 16989428980618779589836661)
                    ·
                      refine ⟨1592758966933010586547187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16989428980618779589836661 1592758966933010586547187)
                      ·
                        rfl

theorem cell23_3101887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_3101887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101887 prefixEnd_3101887 := by exact prefixLift 3101887
  have htrace : WordTrace (prefixWord ++ tailWord_3101887) baseStart_3101887 baseEnd_3101887 := by
    simpa [prefixWord, tailWord_3101887, baseEnd_3101887] using wordTrace_append hprefix tailTrace_3101887
  have hstable : (prefixWord ++ tailWord_3101887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101887).length < 2 ^ (prefixWord ++ tailWord_3101887).sum := by decide
  have hdescent : baseEnd_3101887 < baseStart_3101887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101907 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 4, 6]
def baseStart_3101907 : Nat := 118140960795 + 3101907 * 2 ^ 59
def prefixEnd_3101907 : Nat := 4983230072969 + 3 ^ 40 * 3101907 * 2
def baseEnd_3101907 : Nat := 530923078848700169432365

theorem tailTrace_3101907 : CollatzResearch.WordTrace tailWord_3101907 prefixEnd_3101907 530923078848700169432365 := by
  unfold tailWord_3101907
  simp only [CollatzResearch.WordTrace]
  refine ⟨113135842773328177384079975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75423895182218784922719983 113135842773328177384079975)
  ·
    refine ⟨169703764159992266076119963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113135842773328177384079975 169703764159992266076119963)
    ·
      refine ⟨254555646239988399114179945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169703764159992266076119963 254555646239988399114179945)
      ·
        refine ⟨190916734679991299335634959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254555646239988399114179945 190916734679991299335634959)
        ·
          refine ⟨286375102019986949003452439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190916734679991299335634959 286375102019986949003452439)
          ·
            refine ⟨429562653029980423505178659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286375102019986949003452439 429562653029980423505178659)
            ·
              refine ⟨644343979544970635257767989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429562653029980423505178659 644343979544970635257767989)
              ·
                refine ⟨60407248082340997055415749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 644343979544970635257767989 60407248082340997055415749)
                ·
                  refine ⟨11326359015438936947890453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60407248082340997055415749 11326359015438936947890453)
                  ·
                    refine ⟨530923078848700169432365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11326359015438936947890453 530923078848700169432365)
                    ·
                      rfl

theorem cell23_3101907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 6].length) (baseStart_3101907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101907 prefixEnd_3101907 := by exact prefixLift 3101907
  have htrace : WordTrace (prefixWord ++ tailWord_3101907) baseStart_3101907 baseEnd_3101907 := by
    simpa [prefixWord, tailWord_3101907, baseEnd_3101907] using wordTrace_append hprefix tailTrace_3101907
  have hstable : (prefixWord ++ tailWord_3101907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101907).length < 2 ^ (prefixWord ++ tailWord_3101907).sum := by decide
  have hdescent : baseEnd_3101907 < baseStart_3101907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101909 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3101909 : Nat := 118140960795 + 3101909 * 2 ^ 59
def prefixEnd_3101909 : Nat := 4983230072969 + 3 ^ 40 * 3101909 * 2
def baseEnd_3101909 : Nat := 1592770263507409500472087

theorem tailTrace_3101909 : CollatzResearch.WordTrace tailWord_3101909 prefixEnd_3101909 1592770263507409500472087 := by
  unfold tailWord_3101909
  simp only [CollatzResearch.WordTrace]
  refine ⟨113135915719320931725652781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75423943812880621150435187 113135915719320931725652781)
  ·
    refine ⟨42425968394745349397119793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113135915719320931725652781 42425968394745349397119793)
    ·
      refine ⟨31819476296059012047839845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42425968394745349397119793 31819476296059012047839845)
      ·
        refine ⟨5966151805511064758969971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31819476296059012047839845 5966151805511064758969971)
        ·
          refine ⟨8949227708266597138454957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966151805511064758969971 8949227708266597138454957)
          ·
            refine ⟨3355960390599973926920609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8949227708266597138454957 3355960390599973926920609)
            ·
              refine ⟨2516970292949980445190457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355960390599973926920609 2516970292949980445190457)
              ·
                refine ⟨1887727719712485333892843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516970292949980445190457 1887727719712485333892843)
                ·
                  refine ⟨2831591579568728000839265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887727719712485333892843 2831591579568728000839265)
                  ·
                    refine ⟨2123693684676546000629449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831591579568728000839265 2123693684676546000629449)
                    ·
                      refine ⟨1592770263507409500472087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123693684676546000629449 1592770263507409500472087)
                      ·
                        rfl

theorem cell23_3101909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3101909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101909 prefixEnd_3101909 := by exact prefixLift 3101909
  have htrace : WordTrace (prefixWord ++ tailWord_3101909) baseStart_3101909 baseEnd_3101909 := by
    simpa [prefixWord, tailWord_3101909, baseEnd_3101909] using wordTrace_append hprefix tailTrace_3101909
  have hstable : (prefixWord ++ tailWord_3101909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101909).length < 2 ^ (prefixWord ++ tailWord_3101909).sum := by decide
  have hdescent : baseEnd_3101909 < baseStart_3101909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101931 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 1, 4, 2]
def baseStart_3101931 : Nat := 118140960795 + 3101931 * 2 ^ 59
def prefixEnd_3101931 : Nat := 4983230072969 + 3 ^ 40 * 3101931 * 2
def baseEnd_3101931 : Nat := 1592781560081808414396985

theorem tailTrace_3101931 : CollatzResearch.WordTrace tailWord_3101931 prefixEnd_3101931 1592781560081808414396985 := by
  unfold tailWord_3101931
  simp only [CollatzResearch.WordTrace]
  refine ⟨113136718125241229482953647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75424478750160819655302431 113136718125241229482953647)
  ·
    refine ⟨169705077187861844224430471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113136718125241229482953647 169705077187861844224430471)
    ·
      refine ⟨254557615781792766336645707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169705077187861844224430471 254557615781792766336645707)
      ·
        refine ⟨381836423672689149504968561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254557615781792766336645707 381836423672689149504968561)
        ·
          refine ⟨286377317754516862128726421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381836423672689149504968561 286377317754516862128726421)
          ·
            refine ⟨13423936769742977912284051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 286377317754516862128726421 13423936769742977912284051)
            ·
              refine ⟨20135905154614466868426077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13423936769742977912284051 20135905154614466868426077)
              ·
                refine ⟨7550964432980425075659779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20135905154614466868426077 7550964432980425075659779)
                ·
                  refine ⟨11326446649470637613489669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550964432980425075659779 11326446649470637613489669)
                  ·
                    refine ⟨2123708746775744552529313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11326446649470637613489669 2123708746775744552529313)
                    ·
                      refine ⟨1592781560081808414396985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123708746775744552529313 1592781560081808414396985)
                      ·
                        rfl

theorem cell23_3101931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4, 2].length) (baseStart_3101931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101931 prefixEnd_3101931 := by exact prefixLift 3101931
  have htrace : WordTrace (prefixWord ++ tailWord_3101931) baseStart_3101931 baseEnd_3101931 := by
    simpa [prefixWord, tailWord_3101931, baseEnd_3101931] using wordTrace_append hprefix tailTrace_3101931
  have hstable : (prefixWord ++ tailWord_3101931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101931).length < 2 ^ (prefixWord ++ tailWord_3101931).sum := by decide
  have hdescent : baseEnd_3101931 < baseStart_3101931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101934 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3101934 : Nat := 118140960795 + 3101934 * 2 ^ 59
def prefixEnd_3101934 : Nat := 4983230072969 + 3 ^ 40 * 3101934 * 2
def baseEnd_3101934 : Nat := 1592783100523771902659471

theorem tailTrace_3101934 : CollatzResearch.WordTrace tailWord_3101934 prefixEnd_3101934 1592783100523771902659471 := by
  unfold tailWord_3101934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142103443028795124414107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75424551696153573996875237 14142103443028795124414107)
  ·
    refine ⟨21213155164543192686621161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14142103443028795124414107 21213155164543192686621161)
    ·
      refine ⟨15909866373407394514965871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21213155164543192686621161 15909866373407394514965871)
      ·
        refine ⟨23864799560111091772448807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15909866373407394514965871 23864799560111091772448807)
        ·
          refine ⟨35797199340166637658673211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23864799560111091772448807 35797199340166637658673211)
          ·
            refine ⟨53695799010249956488009817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35797199340166637658673211 53695799010249956488009817)
            ·
              refine ⟨40271849257687467366007363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53695799010249956488009817 40271849257687467366007363)
              ·
                refine ⟨60407773886531201049011045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40271849257687467366007363 60407773886531201049011045)
                ·
                  refine ⟨11326457603724600196689571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60407773886531201049011045 11326457603724600196689571)
                  ·
                    refine ⟨16989686405586900295034357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11326457603724600196689571 16989686405586900295034357)
                    ·
                      refine ⟨1592783100523771902659471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16989686405586900295034357 1592783100523771902659471)
                      ·
                        rfl

theorem cell23_3101934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3101934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3101934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3101934 prefixEnd_3101934 := by exact prefixLift 3101934
  have htrace : WordTrace (prefixWord ++ tailWord_3101934) baseStart_3101934 baseEnd_3101934 := by
    simpa [prefixWord, tailWord_3101934, baseEnd_3101934] using wordTrace_append hprefix tailTrace_3101934
  have hstable : (prefixWord ++ tailWord_3101934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101934).length < 2 ^ (prefixWord ++ tailWord_3101934).sum := by decide
  have hdescent : baseEnd_3101934 < baseStart_3101934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102021 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 4, 4, 2]
def baseStart_3102021 : Nat := 118140960795 + 3102021 * 2 ^ 59
def prefixEnd_3102021 : Nat := 4983230072969 + 3 ^ 40 * 3102021 * 2
def baseEnd_3102021 : Nat := 1592827773340713062271571

theorem tailTrace_3102021 : CollatzResearch.WordTrace tailWord_3102021 prefixEnd_3102021 1592827773340713062271571 := by
  unfold tailWord_3102021
  simp only [CollatzResearch.WordTrace]
  refine ⟨113140000694915174853729917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75426667129943449902486611 113140000694915174853729917)
  ·
    refine ⟨42427500260593190570148719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113140000694915174853729917 42427500260593190570148719)
    ·
      refine ⟨63641250390889785855223079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42427500260593190570148719 63641250390889785855223079)
      ·
        refine ⟨95461875586334678782834619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63641250390889785855223079 95461875586334678782834619)
        ·
          refine ⟨143192813379502018174251929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95461875586334678782834619 143192813379502018174251929)
          ·
            refine ⟨107394610034626513630688947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143192813379502018174251929 107394610034626513630688947)
            ·
              refine ⟨161091915051939770446033421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107394610034626513630688947 161091915051939770446033421)
              ·
                refine ⟨60409468144477413917262533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161091915051939770446033421 60409468144477413917262533)
                ·
                  refine ⟨11326775277089515109486725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60409468144477413917262533 11326775277089515109486725)
                  ·
                    refine ⟨2123770364454284083028761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11326775277089515109486725 2123770364454284083028761)
                    ·
                      refine ⟨1592827773340713062271571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123770364454284083028761 1592827773340713062271571)
                      ·
                        rfl

theorem cell23_3102021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_3102021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102021 prefixEnd_3102021 := by exact prefixLift 3102021
  have htrace : WordTrace (prefixWord ++ tailWord_3102021) baseStart_3102021 baseEnd_3102021 := by
    simpa [prefixWord, tailWord_3102021, baseEnd_3102021] using wordTrace_append hprefix tailTrace_3102021
  have hstable : (prefixWord ++ tailWord_3102021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102021).length < 2 ^ (prefixWord ++ tailWord_3102021).sum := by decide
  have hdescent : baseEnd_3102021 < baseStart_3102021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102022 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3102022 : Nat := 118140960795 + 3102022 * 2 ^ 59
def prefixEnd_3102022 : Nat := 4983230072969 + 3 ^ 40 * 3102022 * 2
def baseEnd_3102022 : Nat := 176980920757929728706563

theorem tailTrace_3102022 : CollatzResearch.WordTrace tailWord_3102022 prefixEnd_3102022 176980920757929728706563 := by
  unfold tailWord_3102022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535626161497236000766135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75426691445274368016344213 3535626161497236000766135)
  ·
    refine ⟨5303439242245854001149203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535626161497236000766135 5303439242245854001149203)
    ·
      refine ⟨7955158863368781001723805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5303439242245854001149203 7955158863368781001723805)
      ·
        refine ⟨2983184573763292875646427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7955158863368781001723805 2983184573763292875646427)
        ·
          refine ⟨4474776860644939313469641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983184573763292875646427 4474776860644939313469641)
          ·
            refine ⟨3356082645483704485102231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474776860644939313469641 3356082645483704485102231)
            ·
              refine ⟨5034123968225556727653347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356082645483704485102231 5034123968225556727653347)
              ·
                refine ⟨7551185952338335091480021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034123968225556727653347 7551185952338335091480021)
                ·
                  refine ⟨176980920757929728706563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7551185952338335091480021 176980920757929728706563)
                  ·
                    rfl

theorem cell23_3102022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3102022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102022 prefixEnd_3102022 := by exact prefixLift 3102022
  have htrace : WordTrace (prefixWord ++ tailWord_3102022) baseStart_3102022 baseEnd_3102022 := by
    simpa [prefixWord, tailWord_3102022, baseEnd_3102022] using wordTrace_append hprefix tailTrace_3102022
  have hstable : (prefixWord ++ tailWord_3102022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102022).length < 2 ^ (prefixWord ++ tailWord_3102022).sum := by decide
  have hdescent : baseEnd_3102022 < baseStart_3102022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102125 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3102125 : Nat := 118140960795 + 3102125 * 2 ^ 59
def prefixEnd_3102125 : Nat := 4983230072969 + 3 ^ 40 * 3102125 * 2
def baseEnd_3102125 : Nat := 530960391776260218457031

theorem tailTrace_3102125 : CollatzResearch.WordTrace tailWord_3102125 prefixEnd_3102125 530960391776260218457031 := by
  unfold tailWord_3102125
  simp only [CollatzResearch.WordTrace]
  refine ⟨113143793886538400615515829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75429195924358933743677219 113143793886538400615515829)
  ·
    refine ⟨10607230676862975057704609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113143793886538400615515829 10607230676862975057704609)
    ·
      refine ⟨7955423007647231293278457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10607230676862975057704609 7955423007647231293278457)
      ·
        refine ⟨5966567255735423469958843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7955423007647231293278457 5966567255735423469958843)
        ·
          refine ⟨8949850883603135204938265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966567255735423469958843 8949850883603135204938265)
          ·
            refine ⟨6712388162702351403703699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8949850883603135204938265 6712388162702351403703699)
            ·
              refine ⟨10068582244053527105555549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712388162702351403703699 10068582244053527105555549)
              ·
                refine ⟨3775718341520072664583331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10068582244053527105555549 3775718341520072664583331)
                ·
                  refine ⟨5663577512280108996874997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775718341520072664583331 5663577512280108996874997)
                  ·
                    refine ⟨530960391776260218457031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5663577512280108996874997 530960391776260218457031)
                    ·
                      rfl

theorem cell23_3102125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3102125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102125 prefixEnd_3102125 := by exact prefixLift 3102125
  have htrace : WordTrace (prefixWord ++ tailWord_3102125) baseStart_3102125 baseEnd_3102125 := by
    simpa [prefixWord, tailWord_3102125, baseEnd_3102125] using wordTrace_append hprefix tailTrace_3102125
  have hstable : (prefixWord ++ tailWord_3102125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102125).length < 2 ^ (prefixWord ++ tailWord_3102125).sum := by decide
  have hdescent : baseEnd_3102125 < baseStart_3102125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102141 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3102141 : Nat := 118140960795 + 3102141 * 2 ^ 59
def prefixEnd_3102141 : Nat := 4983230072969 + 3 ^ 40 * 3102141 * 2
def baseEnd_3102141 : Nat := 1592889391019252592771019

theorem tailTrace_3102141 : CollatzResearch.WordTrace tailWord_3102141 prefixEnd_3102141 1592889391019252592771019 := by
  unfold tailWord_3102141
  simp only [CollatzResearch.WordTrace]
  refine ⟨113144377454480435348098277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75429584969653623565398851 113144377454480435348098277)
  ·
    refine ⟨21214570772715081627768427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113144377454480435348098277 21214570772715081627768427)
    ·
      refine ⟨31821856159072622441652641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21214570772715081627768427 31821856159072622441652641)
      ·
        refine ⟨23866392119304466831239481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31821856159072622441652641 23866392119304466831239481)
        ·
          refine ⟨17899794089478350123429611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23866392119304466831239481 17899794089478350123429611)
          ·
            refine ⟨26849691134217525185144417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17899794089478350123429611 26849691134217525185144417)
            ·
              refine ⟨20137268350663143888858313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26849691134217525185144417 20137268350663143888858313)
              ·
                refine ⟨15102951262997357916643735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20137268350663143888858313 15102951262997357916643735)
                ·
                  refine ⟨22654426894496036874965603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15102951262997357916643735 22654426894496036874965603)
                  ·
                    refine ⟨33981640341744055312448405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22654426894496036874965603 33981640341744055312448405)
                    ·
                      refine ⟨1592889391019252592771019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33981640341744055312448405 1592889391019252592771019)
                      ·
                        rfl

theorem cell23_3102141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3102141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102141 prefixEnd_3102141 := by exact prefixLift 3102141
  have htrace : WordTrace (prefixWord ++ tailWord_3102141) baseStart_3102141 baseEnd_3102141 := by
    simpa [prefixWord, tailWord_3102141, baseEnd_3102141] using wordTrace_append hprefix tailTrace_3102141
  have hstable : (prefixWord ++ tailWord_3102141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102141).length < 2 ^ (prefixWord ++ tailWord_3102141).sum := by decide
  have hdescent : baseEnd_3102141 < baseStart_3102141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102146 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3102146 : Nat := 118140960795 + 3102146 * 2 ^ 59
def prefixEnd_3102146 : Nat := 4983230072969 + 3 ^ 40 * 3102146 * 2
def baseEnd_3102146 : Nat := 176987995380280563689833

theorem tailTrace_3102146 : CollatzResearch.WordTrace tailWord_3102146 prefixEnd_3102146 176987995380280563689833 := by
  unfold tailWord_3102146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28286139954865580300507573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75429706546308214134686861 28286139954865580300507573)
  ·
    refine ⟨2651825620768648153172585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28286139954865580300507573 2651825620768648153172585)
    ·
      refine ⟨1988869215576486114879439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2651825620768648153172585 1988869215576486114879439)
      ·
        refine ⟨2983303823364729172319159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988869215576486114879439 2983303823364729172319159)
        ·
          refine ⟨4474955735047093758478739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983303823364729172319159 4474955735047093758478739)
          ·
            refine ⟨6712433602570640637718109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474955735047093758478739 6712433602570640637718109)
            ·
              refine ⟨2517162600963990239144291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6712433602570640637718109 2517162600963990239144291)
              ·
                refine ⟨3775743901445985358716437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517162600963990239144291 3775743901445985358716437)
                ·
                  refine ⟨176987995380280563689833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3775743901445985358716437 176987995380280563689833)
                  ·
                    rfl

theorem cell23_3102146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3102146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102146 prefixEnd_3102146 := by exact prefixLift 3102146
  have htrace : WordTrace (prefixWord ++ tailWord_3102146) baseStart_3102146 baseEnd_3102146 := by
    simpa [prefixWord, tailWord_3102146, baseEnd_3102146] using wordTrace_append hprefix tailTrace_3102146
  have hstable : (prefixWord ++ tailWord_3102146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102146).length < 2 ^ (prefixWord ++ tailWord_3102146).sum := by decide
  have hdescent : baseEnd_3102146 < baseStart_3102146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102148 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3102148 : Nat := 118140960795 + 3102148 * 2 ^ 59
def prefixEnd_3102148 : Nat := 4983230072969 + 3 ^ 40 * 3102148 * 2
def baseEnd_3102148 : Nat := 1592892985383834065383487

theorem tailTrace_3102148 : CollatzResearch.WordTrace tailWord_3102148 prefixEnd_3102148 1592892985383834065383487 := by
  unfold tailWord_3102148
  simp only [CollatzResearch.WordTrace]
  refine ⟨56572316382727537771801549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75429755176970050362402065 56572316382727537771801549)
  ·
    refine ⟨21214618643522826664425581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56572316382727537771801549 21214618643522826664425581)
    ·
      refine ⟨7955481991321059999159593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21214618643522826664425581 7955481991321059999159593)
      ·
        refine ⟨5966611493490794999369695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7955481991321059999159593 5966611493490794999369695)
        ·
          refine ⟨8949917240236192499054543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966611493490794999369695 8949917240236192499054543)
          ·
            refine ⟨13424875860354288748581815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8949917240236192499054543 13424875860354288748581815)
            ·
              refine ⟨20137313790531433122872723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13424875860354288748581815 20137313790531433122872723)
              ·
                refine ⟨30205970685797149684309085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20137313790531433122872723 30205970685797149684309085)
                ·
                  refine ⟨11327239007173931131615907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30205970685797149684309085 11327239007173931131615907)
                  ·
                    refine ⟨16990858510760896697423861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11327239007173931131615907 16990858510760896697423861)
                    ·
                      refine ⟨1592892985383834065383487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16990858510760896697423861 1592892985383834065383487)
                      ·
                        rfl

theorem cell23_3102148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3102148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102148 prefixEnd_3102148 := by exact prefixLift 3102148
  have htrace : WordTrace (prefixWord ++ tailWord_3102148) baseStart_3102148 baseEnd_3102148 := by
    simpa [prefixWord, tailWord_3102148, baseEnd_3102148] using wordTrace_append hprefix tailTrace_3102148
  have hstable : (prefixWord ++ tailWord_3102148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102148).length < 2 ^ (prefixWord ++ tailWord_3102148).sum := by decide
  have hdescent : baseEnd_3102148 < baseStart_3102148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102158 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_3102158 : Nat := 118140960795 + 3102158 * 2 ^ 59
def prefixEnd_3102158 : Nat := 4983230072969 + 3 ^ 40 * 3102158 * 2
def baseEnd_3102158 : Nat := 1592898120190379026258441

theorem tailTrace_3102158 : CollatzResearch.WordTrace tailWord_3102158 prefixEnd_3102158 1592898120190379026258441 := by
  unfold tailWord_3102158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143124686927355906433391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75429998330279231500978085 14143124686927355906433391)
  ·
    refine ⟨21214687030391033859650087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14143124686927355906433391 21214687030391033859650087)
    ·
      refine ⟨31822030545586550789475131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21214687030391033859650087 31822030545586550789475131)
      ·
        refine ⟨47733045818379826184212697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31822030545586550789475131 47733045818379826184212697)
        ·
          refine ⟨35799784363784869638159523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47733045818379826184212697 35799784363784869638159523)
          ·
            refine ⟨53699676545677304457239285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35799784363784869638159523 53699676545677304457239285)
            ·
              refine ⟨5034344676157247292866183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53699676545677304457239285 5034344676157247292866183)
              ·
                refine ⟨7551517014235870939299275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034344676157247292866183 7551517014235870939299275)
                ·
                  refine ⟨11327275521353806408948913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7551517014235870939299275 11327275521353806408948913)
                  ·
                    refine ⟨8495456641015354806711685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11327275521353806408948913 8495456641015354806711685)
                    ·
                      refine ⟨1592898120190379026258441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8495456641015354806711685 1592898120190379026258441)
                      ·
                        rfl

theorem cell23_3102158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_3102158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102158 prefixEnd_3102158 := by exact prefixLift 3102158
  have htrace : WordTrace (prefixWord ++ tailWord_3102158) baseStart_3102158 baseEnd_3102158 := by
    simpa [prefixWord, tailWord_3102158, baseEnd_3102158] using wordTrace_append hprefix tailTrace_3102158
  have hstable : (prefixWord ++ tailWord_3102158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102158).length < 2 ^ (prefixWord ++ tailWord_3102158).sum := by decide
  have hdescent : baseEnd_3102158 < baseStart_3102158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102165 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3102165 : Nat := 118140960795 + 3102165 * 2 ^ 59
def prefixEnd_3102165 : Nat := 4983230072969 + 3 ^ 40 * 3102165 * 2
def baseEnd_3102165 : Nat := 1592901714554960498870909

theorem tailTrace_3102165 : CollatzResearch.WordTrace tailWord_3102165 prefixEnd_3102165 1592901714554960498870909 := by
  unfold tailWord_3102165
  simp only [CollatzResearch.WordTrace]
  refine ⟨113145252806393487446971949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75430168537595658297981299 113145252806393487446971949)
  ·
    refine ⟨42429469802397557792614481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113145252806393487446971949 42429469802397557792614481)
    ·
      refine ⟨31822102351798168344460861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42429469802397557792614481 31822102351798168344460861)
      ·
        refine ⟨11933288381924313129172823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31822102351798168344460861 11933288381924313129172823)
        ·
          refine ⟨17899932572886469693759235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11933288381924313129172823 17899932572886469693759235)
          ·
            refine ⟨26849898859329704540638853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17899932572886469693759235 26849898859329704540638853)
            ·
              refine ⟨5034356036124319601369785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26849898859329704540638853 5034356036124319601369785)
              ·
                refine ⟨3775767027093239701027339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5034356036124319601369785 3775767027093239701027339)
                ·
                  refine ⟨5663650540639859551541009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775767027093239701027339 5663650540639859551541009)
                  ·
                    refine ⟨4247737905479894663655757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5663650540639859551541009 4247737905479894663655757)
                    ·
                      refine ⟨1592901714554960498870909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4247737905479894663655757 1592901714554960498870909)
                      ·
                        rfl

theorem cell23_3102165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3102165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102165 prefixEnd_3102165 := by exact prefixLift 3102165
  have htrace : WordTrace (prefixWord ++ tailWord_3102165) baseStart_3102165 baseEnd_3102165 := by
    simpa [prefixWord, tailWord_3102165, baseEnd_3102165] using wordTrace_append hprefix tailTrace_3102165
  have hstable : (prefixWord ++ tailWord_3102165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102165).length < 2 ^ (prefixWord ++ tailWord_3102165).sum := by decide
  have hdescent : baseEnd_3102165 < baseStart_3102165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102179 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 1, 2, 2]
def baseStart_3102179 : Nat := 118140960795 + 3102179 * 2 ^ 59
def prefixEnd_3102179 : Nat := 4983230072969 + 3 ^ 40 * 3102179 * 2
def baseEnd_3102179 : Nat := 1592908903284123444095845

theorem tailTrace_3102179 : CollatzResearch.WordTrace tailWord_3102179 prefixEnd_3102179 1592908903284123444095845 := by
  unfold tailWord_3102179
  simp only [CollatzResearch.WordTrace]
  refine ⟨113145763428342767837981591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75430508952228511891987727 113145763428342767837981591)
  ·
    refine ⟨169718645142514151756972387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113145763428342767837981591 169718645142514151756972387)
    ·
      refine ⟨254577967713771227635458581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169718645142514151756972387 254577967713771227635458581)
      ·
        refine ⟨11933342236583026295412121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 254577967713771227635458581 11933342236583026295412121)
        ·
          refine ⟨8950006677437269721559091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11933342236583026295412121 8950006677437269721559091)
          ·
            refine ⟨13425010016155904582338637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8950006677437269721559091 13425010016155904582338637)
            ·
              refine ⟨5034378756058464218376989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13425010016155904582338637 5034378756058464218376989)
              ·
                refine ⟨1887892033521924081891371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5034378756058464218376989 1887892033521924081891371)
                ·
                  refine ⟨2831838050282886122837057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887892033521924081891371 2831838050282886122837057)
                  ·
                    refine ⟨2123878537712164592127793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2831838050282886122837057 2123878537712164592127793)
                    ·
                      refine ⟨1592908903284123444095845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123878537712164592127793 1592908903284123444095845)
                      ·
                        rfl

theorem cell23_3102179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_3102179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102179 prefixEnd_3102179 := by exact prefixLift 3102179
  have htrace : WordTrace (prefixWord ++ tailWord_3102179) baseStart_3102179 baseEnd_3102179 := by
    simpa [prefixWord, tailWord_3102179, baseEnd_3102179] using wordTrace_append hprefix tailTrace_3102179
  have hstable : (prefixWord ++ tailWord_3102179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102179).length < 2 ^ (prefixWord ++ tailWord_3102179).sum := by decide
  have hdescent : baseEnd_3102179 < baseStart_3102179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102201 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3102201 : Nat := 118140960795 + 3102201 * 2 ^ 59
def prefixEnd_3102201 : Nat := 4983230072969 + 3 ^ 40 * 3102201 * 2
def baseEnd_3102201 : Nat := 1592920199858522358020743

theorem tailTrace_3102201 : CollatzResearch.WordTrace tailWord_3102201 prefixEnd_3102201 1592920199858522358020743 := by
  unfold tailWord_3102201
  simp only [CollatzResearch.WordTrace]
  refine ⟨113146565834263065595282457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75431043889508710396854971 113146565834263065595282457)
  ·
    refine ⟨84859924375697299196461843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113146565834263065595282457 84859924375697299196461843)
    ·
      refine ⟨127289886563545948794692765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84859924375697299196461843 127289886563545948794692765)
      ·
        refine ⟨47733707461329730798009787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127289886563545948794692765 47733707461329730798009787)
        ·
          refine ⟨71600561191994596197014681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47733707461329730798009787 71600561191994596197014681)
          ·
            refine ⟨53700420893995947147761011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71600561191994596197014681 53700420893995947147761011)
            ·
              refine ⟨80550631340993920721641517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53700420893995947147761011 80550631340993920721641517)
              ·
                refine ⟨30206486752872720270615569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80550631340993920721641517 30206486752872720270615569)
                ·
                  refine ⟨22654865064654540202961677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30206486752872720270615569 22654865064654540202961677)
                  ·
                    refine ⟨8495574399245452576110629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22654865064654540202961677 8495574399245452576110629)
                    ·
                      refine ⟨1592920199858522358020743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8495574399245452576110629 1592920199858522358020743)
                      ·
                        rfl

theorem cell23_3102201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3102201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102201 prefixEnd_3102201 := by exact prefixLift 3102201
  have htrace : WordTrace (prefixWord ++ tailWord_3102201) baseStart_3102201 baseEnd_3102201 := by
    simpa [prefixWord, tailWord_3102201, baseEnd_3102201] using wordTrace_append hprefix tailTrace_3102201
  have hstable : (prefixWord ++ tailWord_3102201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102201).length < 2 ^ (prefixWord ++ tailWord_3102201).sum := by decide
  have hdescent : baseEnd_3102201 < baseStart_3102201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102206 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3102206 : Nat := 118140960795 + 3102206 * 2 ^ 59
def prefixEnd_3102206 : Nat := 4983230072969 + 3 ^ 40 * 3102206 * 2
def baseEnd_3102206 : Nat := 530974255753931612819407

theorem tailTrace_3102206 : CollatzResearch.WordTrace tailWord_3102206 prefixEnd_3102206 530974255753931612819407 := by
  unfold tailWord_3102206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143343524905618931151809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75431165466163300966142981 14143343524905618931151809)
  ·
    refine ⟨10607507643679214198363857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14143343524905618931151809 10607507643679214198363857)
    ·
      refine ⟨7955630732759410648772893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10607507643679214198363857 7955630732759410648772893)
      ·
        refine ⟨2983361524784778993289835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7955630732759410648772893 2983361524784778993289835)
        ·
          refine ⟨4475042287177168489934753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983361524784778993289835 4475042287177168489934753)
          ·
            refine ⟨3356281715382876367451065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475042287177168489934753 3356281715382876367451065)
            ·
              refine ⟨2517211286537157275588299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3356281715382876367451065 2517211286537157275588299)
              ·
                refine ⟨3775816929805735913382449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517211286537157275588299 3775816929805735913382449)
                ·
                  refine ⟨2831862697354301935036837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3775816929805735913382449 2831862697354301935036837)
                  ·
                    refine ⟨530974255753931612819407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831862697354301935036837 530974255753931612819407)
                    ·
                      rfl

theorem cell23_3102206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3102206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102206 prefixEnd_3102206 := by exact prefixLift 3102206
  have htrace : WordTrace (prefixWord ++ tailWord_3102206) baseStart_3102206 baseEnd_3102206 := by
    simpa [prefixWord, tailWord_3102206, baseEnd_3102206] using wordTrace_append hprefix tailTrace_3102206
  have hstable : (prefixWord ++ tailWord_3102206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102206).length < 2 ^ (prefixWord ++ tailWord_3102206).sum := by decide
  have hdescent : baseEnd_3102206 < baseStart_3102206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102222 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_3102222 : Nat := 118140960795 + 3102222 * 2 ^ 59
def prefixEnd_3102222 : Nat := 4983230072969 + 3 ^ 40 * 3102222 * 2
def baseEnd_3102222 : Nat := 1592930982952266775858147

theorem tailTrace_3102222 : CollatzResearch.WordTrace tailWord_3102222 prefixEnd_3102222 1592930982952266775858147 := by
  unfold tailWord_3102222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143416470898373272724615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75431554511457990787864613 14143416470898373272724615)
  ·
    refine ⟨21215124706347559909086923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14143416470898373272724615 21215124706347559909086923)
    ·
      refine ⟨31822687059521339863630385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21215124706347559909086923 31822687059521339863630385)
      ·
        refine ⟨23867015294641004897722789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31822687059521339863630385 23867015294641004897722789)
        ·
          refine ⟨4475065367745188418323023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23867015294641004897722789 4475065367745188418323023)
          ·
            refine ⟨6712598051617782627484535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475065367745188418323023 6712598051617782627484535)
            ·
              refine ⟨10068897077426673941226803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712598051617782627484535 10068897077426673941226803)
              ·
                refine ⟨15103345616140010911840205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10068897077426673941226803 15103345616140010911840205)
                ·
                  refine ⟨5663754606052504091940077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15103345616140010911840205 5663754606052504091940077)
                  ·
                    refine ⟨2123907977269689034477529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5663754606052504091940077 2123907977269689034477529)
                    ·
                      refine ⟨1592930982952266775858147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2123907977269689034477529 1592930982952266775858147)
                      ·
                        rfl

theorem cell23_3102222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_3102222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102222 prefixEnd_3102222 := by exact prefixLift 3102222
  have htrace : WordTrace (prefixWord ++ tailWord_3102222) baseStart_3102222 baseEnd_3102222 := by
    simpa [prefixWord, tailWord_3102222, baseEnd_3102222] using wordTrace_append hprefix tailTrace_3102222
  have hstable : (prefixWord ++ tailWord_3102222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102222).length < 2 ^ (prefixWord ++ tailWord_3102222).sum := by decide
  have hdescent : baseEnd_3102222 < baseStart_3102222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102281 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_3102281 : Nat := 118140960795 + 3102281 * 2 ^ 59
def prefixEnd_3102281 : Nat := 4983230072969 + 3 ^ 40 * 3102281 * 2
def baseEnd_3102281 : Nat := 1592961278310882045020375

theorem tailTrace_3102281 : CollatzResearch.WordTrace tailWord_3102281 prefixEnd_3102281 1592961278310882045020375 := by
  unfold tailWord_3102281
  simp only [CollatzResearch.WordTrace]
  refine ⟨113149483673973239258194697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75432989115982159505463131 113149483673973239258194697)
  ·
    refine ⟨84862112755479929443646023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113149483673973239258194697 84862112755479929443646023)
    ·
      refine ⟨127293169133219894165469035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84862112755479929443646023 127293169133219894165469035)
      ·
        refine ⟨190939753699829841248203553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127293169133219894165469035 190939753699829841248203553)
        ·
          refine ⟨143204815274872380936152665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190939753699829841248203553 143204815274872380936152665)
          ·
            refine ⟨107403611456154285702114499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143204815274872380936152665 107403611456154285702114499)
            ·
              refine ⟨161105417184231428553171749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107403611456154285702114499 161105417184231428553171749)
              ·
                refine ⟨30207265722043392853719703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161105417184231428553171749 30207265722043392853719703)
                ·
                  refine ⟨45310898583065089280579555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30207265722043392853719703 45310898583065089280579555)
                  ·
                    refine ⟨67966347874597633920869333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45310898583065089280579555 67966347874597633920869333)
                    ·
                      refine ⟨1592961278310882045020375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67966347874597633920869333 1592961278310882045020375)
                      ·
                        rfl

theorem cell23_3102281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_3102281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102281 prefixEnd_3102281 := by exact prefixLift 3102281
  have htrace : WordTrace (prefixWord ++ tailWord_3102281) baseStart_3102281 baseEnd_3102281 := by
    simpa [prefixWord, tailWord_3102281, baseEnd_3102281] using wordTrace_append hprefix tailTrace_3102281
  have hstable : (prefixWord ++ tailWord_3102281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102281).length < 2 ^ (prefixWord ++ tailWord_3102281).sum := by decide
  have hdescent : baseEnd_3102281 < baseStart_3102281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102325 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3102325 : Nat := 118140960795 + 3102325 * 2 ^ 59
def prefixEnd_3102325 : Nat := 4983230072969 + 3 ^ 40 * 3102325 * 2
def baseEnd_3102325 : Nat := 1592983871459679872870173

theorem tailTrace_3102325 : CollatzResearch.WordTrace tailWord_3102325 prefixEnd_3102325 1592983871459679872870173 := by
  unfold tailWord_3102325
  simp only [CollatzResearch.WordTrace]
  refine ⟨113151088485813834772796429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75434058990542556515197619 113151088485813834772796429)
  ·
    refine ⟨42431658182180188039798661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113151088485813834772796429 42431658182180188039798661)
    ·
      refine ⟨7955935909158785257462249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42431658182180188039798661 7955935909158785257462249)
      ·
        refine ⟨5966951931869088943096687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7955935909158785257462249 5966951931869088943096687)
        ·
          refine ⟨8950427897803633414645031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966951931869088943096687 8950427897803633414645031)
          ·
            refine ⟨13425641846705450121967547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8950427897803633414645031 13425641846705450121967547)
            ·
              refine ⟨20138462770058175182951321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13425641846705450121967547 20138462770058175182951321)
              ·
                refine ⟨15103847077543631387213491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20138462770058175182951321 15103847077543631387213491)
                ·
                  refine ⟨22655770616315447080820237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15103847077543631387213491 22655770616315447080820237)
                  ·
                    refine ⟨8495913981118292655307589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22655770616315447080820237 8495913981118292655307589)
                    ·
                      refine ⟨1592983871459679872870173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8495913981118292655307589 1592983871459679872870173)
                      ·
                        rfl

theorem cell23_3102325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3102325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102325 prefixEnd_3102325 := by exact prefixLift 3102325
  have htrace : WordTrace (prefixWord ++ tailWord_3102325) baseStart_3102325 baseEnd_3102325 := by
    simpa [prefixWord, tailWord_3102325, baseEnd_3102325] using wordTrace_append hprefix tailTrace_3102325
  have hstable : (prefixWord ++ tailWord_3102325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102325).length < 2 ^ (prefixWord ++ tailWord_3102325).sum := by decide
  have hdescent : baseEnd_3102325 < baseStart_3102325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102415 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 4]
def baseStart_3102415 : Nat := 118140960795 + 3102415 * 2 ^ 59
def prefixEnd_3102415 : Nat := 4983230072969 + 3 ^ 40 * 3102415 * 2
def baseEnd_3102415 : Nat := 1593030084718584520744759

theorem tailTrace_3102415 : CollatzResearch.WordTrace tailWord_3102415 prefixEnd_3102415 1593030084718584520744759 := by
  unfold tailWord_3102415
  simp only [CollatzResearch.WordTrace]
  refine ⟨113154371055487780143572699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75436247370325186762381799 113154371055487780143572699)
  ·
    refine ⟨169731556583231670215359049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113154371055487780143572699 169731556583231670215359049)
    ·
      refine ⟨127298667437423752661519287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169731556583231670215359049 127298667437423752661519287)
      ·
        refine ⟨190948001156135628992278931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127298667437423752661519287 190948001156135628992278931)
        ·
          refine ⟨286422001734203443488418397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190948001156135628992278931 286422001734203443488418397)
          ·
            refine ⟨107408250650326291308156899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286422001734203443488418397 107408250650326291308156899)
            ·
              refine ⟨161112375975489436962235349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107408250650326291308156899 161112375975489436962235349)
              ·
                refine ⟨3776071311925533678802391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161112375975489436962235349 3776071311925533678802391)
                ·
                  refine ⟨5664106967888300518203587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776071311925533678802391 5664106967888300518203587)
                  ·
                    refine ⟨8496160451832450777305381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664106967888300518203587 8496160451832450777305381)
                    ·
                      refine ⟨1593030084718584520744759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8496160451832450777305381 1593030084718584520744759)
                      ·
                        rfl

theorem cell23_3102415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_3102415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102415 prefixEnd_3102415 := by exact prefixLift 3102415
  have htrace : WordTrace (prefixWord ++ tailWord_3102415) baseStart_3102415 baseEnd_3102415 := by
    simpa [prefixWord, tailWord_3102415, baseEnd_3102415] using wordTrace_append hprefix tailTrace_3102415
  have hstable : (prefixWord ++ tailWord_3102415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102415).length < 2 ^ (prefixWord ++ tailWord_3102415).sum := by decide
  have hdescent : baseEnd_3102415 < baseStart_3102415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102426 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3]
def baseStart_3102426 : Nat := 118140960795 + 3102426 * 2 ^ 59
def prefixEnd_3102426 : Nat := 4983230072969 + 3 ^ 40 * 3102426 * 2
def baseEnd_3102426 : Nat := 1593035733005783977707209

theorem tailTrace_3102426 : CollatzResearch.WordTrace tailWord_3102426 prefixEnd_3102426 1593035733005783977707209 := by
  unfold tailWord_3102426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28288693064611982255555783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75436514838965286014815421 28288693064611982255555783)
  ·
    refine ⟨42433039596917973383333675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28288693064611982255555783 42433039596917973383333675)
    ·
      refine ⟨63649559395376960075000513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42433039596917973383333675 63649559395376960075000513)
      ·
        refine ⟨47737169546532720056250385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63649559395376960075000513 47737169546532720056250385)
        ·
          refine ⟨35802877159899540042187789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47737169546532720056250385 35802877159899540042187789)
          ·
            refine ⟨13426078934962327515820421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35802877159899540042187789 13426078934962327515820421)
            ·
              refine ⟨2517389800305436409216329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13426078934962327515820421 2517389800305436409216329)
              ·
                refine ⟨1888042350229077306912247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517389800305436409216329 1888042350229077306912247)
                ·
                  refine ⟨2832063525343615960368371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888042350229077306912247 2832063525343615960368371)
                  ·
                    refine ⟨4248095288015423940552557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2832063525343615960368371 4248095288015423940552557)
                    ·
                      refine ⟨1593035733005783977707209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4248095288015423940552557 1593035733005783977707209)
                      ·
                        rfl

theorem cell23_3102426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_3102426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102426 prefixEnd_3102426 := by exact prefixLift 3102426
  have htrace : WordTrace (prefixWord ++ tailWord_3102426) baseStart_3102426 baseEnd_3102426 := by
    simpa [prefixWord, tailWord_3102426, baseEnd_3102426] using wordTrace_append hprefix tailTrace_3102426
  have hstable : (prefixWord ++ tailWord_3102426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102426).length < 2 ^ (prefixWord ++ tailWord_3102426).sum := by decide
  have hdescent : baseEnd_3102426 < baseStart_3102426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102442 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3102442 : Nat := 118140960795 + 3102442 * 2 ^ 59
def prefixEnd_3102442 : Nat := 4983230072969 + 3 ^ 40 * 3102442 * 2
def baseEnd_3102442 : Nat := 531014649565418638369045

theorem tailTrace_3102442 : CollatzResearch.WordTrace tailWord_3102442 prefixEnd_3102442 531014649565418638369045 := by
  unfold tailWord_3102442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28288838956597490938701395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75436903884259975836537053 28288838956597490938701395)
  ·
    refine ⟨42433258434896236408052093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28288838956597490938701395 42433258434896236408052093)
    ·
      refine ⟨15912471913086088653019535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42433258434896236408052093 15912471913086088653019535)
      ·
        refine ⟨23868707869629132979529303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15912471913086088653019535 23868707869629132979529303)
        ·
          refine ⟨35803061804443699469293955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23868707869629132979529303 35803061804443699469293955)
          ·
            refine ⟨53704592706665549203940933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35803061804443699469293955 53704592706665549203940933)
            ·
              refine ⟨10069611132499790475738925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53704592706665549203940933 10069611132499790475738925)
              ·
                refine ⟨3776104174687421428402097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10069611132499790475738925 3776104174687421428402097)
                ·
                  refine ⟨2832078131015566071301573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776104174687421428402097 2832078131015566071301573)
                  ·
                    refine ⟨531014649565418638369045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832078131015566071301573 531014649565418638369045)
                    ·
                      rfl

theorem cell23_3102442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3102442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102442 prefixEnd_3102442 := by exact prefixLift 3102442
  have htrace : WordTrace (prefixWord ++ tailWord_3102442) baseStart_3102442 baseEnd_3102442 := by
    simpa [prefixWord, tailWord_3102442, baseEnd_3102442] using wordTrace_append hprefix tailTrace_3102442
  have hstable : (prefixWord ++ tailWord_3102442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102442).length < 2 ^ (prefixWord ++ tailWord_3102442).sum := by decide
  have hdescent : baseEnd_3102442 < baseStart_3102442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102449 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 3, 2, 2]
def baseStart_3102449 : Nat := 118140960795 + 3102449 * 2 ^ 59
def prefixEnd_3102449 : Nat := 4983230072969 + 3 ^ 40 * 3102449 * 2
def baseEnd_3102449 : Nat := 1593047543060837387719603

theorem tailTrace_3102449 : CollatzResearch.WordTrace tailWord_3102449 prefixEnd_3102449 1593047543060837387719603 := by
  unfold tailWord_3102449
  simp only [CollatzResearch.WordTrace]
  refine ⟨113155611137364603950310401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75437074091576402633540267 113155611137364603950310401)
  ·
    refine ⟨84866708353023452962732801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113155611137364603950310401 84866708353023452962732801)
    ·
      refine ⟨63650031264767589722049601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84866708353023452962732801 63650031264767589722049601)
      ·
        refine ⟨47737523448575692291537201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63650031264767589722049601 47737523448575692291537201)
        ·
          refine ⟨35803142586431769218652901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47737523448575692291537201 35803142586431769218652901)
          ·
            refine ⟨6713089234955956728497419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35803142586431769218652901 6713089234955956728497419)
            ·
              refine ⟨10069633852433935092746129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713089234955956728497419 10069633852433935092746129)
              ·
                refine ⟨7552225389325451319559597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10069633852433935092746129 7552225389325451319559597)
                ·
                  refine ⟨2832084520997044244834849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7552225389325451319559597 2832084520997044244834849)
                  ·
                    refine ⟨2124063390747783183626137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832084520997044244834849 2124063390747783183626137)
                    ·
                      refine ⟨1593047543060837387719603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124063390747783183626137 1593047543060837387719603)
                      ·
                        rfl

theorem cell23_3102449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_3102449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102449 prefixEnd_3102449 := by exact prefixLift 3102449
  have htrace : WordTrace (prefixWord ++ tailWord_3102449) baseStart_3102449 baseEnd_3102449 := by
    simpa [prefixWord, tailWord_3102449, baseEnd_3102449] using wordTrace_append hprefix tailTrace_3102449
  have hstable : (prefixWord ++ tailWord_3102449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102449).length < 2 ^ (prefixWord ++ tailWord_3102449).sum := by decide
  have hdescent : baseEnd_3102449 < baseStart_3102449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102526 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_3102526 : Nat := 118140960795 + 3102526 * 2 ^ 59
def prefixEnd_3102526 : Nat := 4983230072969 + 3 ^ 40 * 3102526 * 2
def baseEnd_3102526 : Nat := 1593087081071233586456749

theorem tailTrace_3102526 : CollatzResearch.WordTrace tailWord_3102526 prefixEnd_3102526 1593087081071233586456749 := by
  unfold tailWord_3102526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14144802444760705762607929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75438946372057097400575621 14144802444760705762607929)
  ·
    refine ⟨10608601833570529321955947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14144802444760705762607929 10608601833570529321955947)
    ·
      refine ⟨15912902750355793982933921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10608601833570529321955947 15912902750355793982933921)
      ·
        refine ⟨11934677062766845487200441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15912902750355793982933921 11934677062766845487200441)
        ·
          refine ⟨8951007797075134115400331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11934677062766845487200441 8951007797075134115400331)
          ·
            refine ⟨13426511695612701173100497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8951007797075134115400331 13426511695612701173100497)
            ·
              refine ⟨10069883771709525879825373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13426511695612701173100497 10069883771709525879825373)
              ·
                refine ⟨3776206414391072204934515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10069883771709525879825373 3776206414391072204934515)
                ·
                  refine ⟨5664309621586608307401773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776206414391072204934515 5664309621586608307401773)
                  ·
                    refine ⟨2124116108094978115275665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5664309621586608307401773 2124116108094978115275665)
                    ·
                      refine ⟨1593087081071233586456749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124116108094978115275665 1593087081071233586456749)
                      ·
                        rfl

theorem cell23_3102526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_3102526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102526 prefixEnd_3102526 := by exact prefixLift 3102526
  have htrace : WordTrace (prefixWord ++ tailWord_3102526) baseStart_3102526 baseEnd_3102526 := by
    simpa [prefixWord, tailWord_3102526, baseEnd_3102526] using wordTrace_append hprefix tailTrace_3102526
  have hstable : (prefixWord ++ tailWord_3102526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102526).length < 2 ^ (prefixWord ++ tailWord_3102526).sum := by decide
  have hdescent : baseEnd_3102526 < baseStart_3102526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102535 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_3102535 : Nat := 118140960795 + 3102535 * 2 ^ 59
def prefixEnd_3102535 : Nat := 4983230072969 + 3 ^ 40 * 3102535 * 2
def baseEnd_3102535 : Nat := 1593091702397124051244207

theorem tailTrace_3102535 : CollatzResearch.WordTrace tailWord_3102535 prefixEnd_3102535 1593091702397124051244207 := by
  unfold tailWord_3102535
  simp only [CollatzResearch.WordTrace]
  refine ⟨113158747815053040637941059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75439165210035360425294039 113158747815053040637941059)
  ·
    refine ⟨169738121722579560956911589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113158747815053040637941059 169738121722579560956911589)
    ·
      refine ⟨31825897822983667679420923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169738121722579560956911589 31825897822983667679420923)
      ·
        refine ⟨47738846734475501519131385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31825897822983667679420923 47738846734475501519131385)
        ·
          refine ⟨35804135050856626139348539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47738846734475501519131385 35804135050856626139348539)
          ·
            refine ⟨53706202576284939209022809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35804135050856626139348539 53706202576284939209022809)
            ·
              refine ⟨40279651932213704406767107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53706202576284939209022809 40279651932213704406767107)
              ·
                refine ⟨60419477898320556610150661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40279651932213704406767107 60419477898320556610150661)
                ·
                  refine ⟨11328652105935104364403249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60419477898320556610150661 11328652105935104364403249)
                  ·
                    refine ⟨8496489079451328273302437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11328652105935104364403249 8496489079451328273302437)
                    ·
                      refine ⟨1593091702397124051244207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8496489079451328273302437 1593091702397124051244207)
                      ·
                        rfl

theorem cell23_3102535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_3102535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102535 prefixEnd_3102535 := by exact prefixLift 3102535
  have htrace : WordTrace (prefixWord ++ tailWord_3102535) baseStart_3102535 baseEnd_3102535 := by
    simpa [prefixWord, tailWord_3102535, baseEnd_3102535] using wordTrace_append hprefix tailTrace_3102535
  have hstable : (prefixWord ++ tailWord_3102535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102535).length < 2 ^ (prefixWord ++ tailWord_3102535).sum := by decide
  have hdescent : baseEnd_3102535 < baseStart_3102535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102585 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3102585 : Nat := 118140960795 + 3102585 * 2 ^ 59
def prefixEnd_3102585 : Nat := 4983230072969 + 3 ^ 40 * 3102585 * 2
def baseEnd_3102585 : Nat := 1593117376429848855618977

theorem tailTrace_3102585 : CollatzResearch.WordTrace tailWord_3102585 prefixEnd_3102585 1593117376429848855618977 := by
  unfold tailWord_3102585
  simp only [CollatzResearch.WordTrace]
  refine ⟨113160571464871899177261209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75440380976581266118174139 113160571464871899177261209)
  ·
    refine ⟨84870428598653924382945907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113160571464871899177261209 84870428598653924382945907)
    ·
      refine ⟨127305642897980886574418861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84870428598653924382945907 127305642897980886574418861)
      ·
        refine ⟨47739616086742832465407073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127305642897980886574418861 47739616086742832465407073)
        ·
          refine ⟨35804712065057124349055305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47739616086742832465407073 35804712065057124349055305)
          ·
            refine ⟨26853534048792843261791479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35804712065057124349055305 26853534048792843261791479)
            ·
              refine ⟨40280301073189264892687219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26853534048792843261791479 40280301073189264892687219)
              ·
                refine ⟨60420451609783897339030829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40280301073189264892687219 60420451609783897339030829)
                ·
                  refine ⟨22657669353668961502136561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60420451609783897339030829 22657669353668961502136561)
                  ·
                    refine ⟨16993252015251721126602421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22657669353668961502136561 16993252015251721126602421)
                    ·
                      refine ⟨1593117376429848855618977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16993252015251721126602421 1593117376429848855618977)
                      ·
                        rfl

theorem cell23_3102585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3102585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102585 prefixEnd_3102585 := by exact prefixLift 3102585
  have htrace : WordTrace (prefixWord ++ tailWord_3102585) baseStart_3102585 baseEnd_3102585 := by
    simpa [prefixWord, tailWord_3102585, baseEnd_3102585] using wordTrace_append hprefix tailTrace_3102585
  have hstable : (prefixWord ++ tailWord_3102585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102585).length < 2 ^ (prefixWord ++ tailWord_3102585).sum := by decide
  have hdescent : baseEnd_3102585 < baseStart_3102585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102590 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3102590 : Nat := 118140960795 + 3102590 * 2 ^ 59
def prefixEnd_3102590 : Nat := 4983230072969 + 3 ^ 40 * 3102590 * 2
def baseEnd_3102590 : Nat := 1593119943833121336056455

theorem tailTrace_3102590 : CollatzResearch.WordTrace tailWord_3102590 prefixEnd_3102590 1593119943833121336056455 := by
  unfold tailWord_3102590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145094228731723128899153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75440502553235856687462149 14145094228731723128899153)
  ·
    refine ⟨10608820671548792346674365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14145094228731723128899153 10608820671548792346674365)
    ·
      refine ⟨3978307751830797130002887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10608820671548792346674365 3978307751830797130002887)
      ·
        refine ⟨5967461627746195695004331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978307751830797130002887 5967461627746195695004331)
        ·
          refine ⟨8951192441619293542506497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5967461627746195695004331 8951192441619293542506497)
          ·
            refine ⟨6713394331214470156879873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8951192441619293542506497 6713394331214470156879873)
            ·
              refine ⟨5035045748410852617659905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713394331214470156879873 5035045748410852617659905)
              ·
                refine ⟨3776284311308139463244929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035045748410852617659905 3776284311308139463244929)
                ·
                  refine ⟨2832213233481104597433697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776284311308139463244929 2832213233481104597433697)
                  ·
                    refine ⟨2124159925110828448075273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832213233481104597433697 2124159925110828448075273)
                    ·
                      refine ⟨1593119943833121336056455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124159925110828448075273 1593119943833121336056455)
                      ·
                        rfl

theorem cell23_3102590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3102590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102590 prefixEnd_3102590 := by exact prefixLift 3102590
  have htrace : WordTrace (prefixWord ++ tailWord_3102590) baseStart_3102590 baseEnd_3102590 := by
    simpa [prefixWord, tailWord_3102590, baseEnd_3102590] using wordTrace_append hprefix tailTrace_3102590
  have hstable : (prefixWord ++ tailWord_3102590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102590).length < 2 ^ (prefixWord ++ tailWord_3102590).sum := by decide
  have hdescent : baseEnd_3102590 < baseStart_3102590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102606 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3102606 : Nat := 118140960795 + 3102606 * 2 ^ 59
def prefixEnd_3102606 : Nat := 4983230072969 + 3 ^ 40 * 3102606 * 2
def baseEnd_3102606 : Nat := 1593128159523593273456381

theorem tailTrace_3102606 : CollatzResearch.WordTrace tailWord_3102606 prefixEnd_3102606 1593128159523593273456381 := by
  unfold tailWord_3102606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145167174724477470471959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75440891598530546509183781 14145167174724477470471959)
  ·
    refine ⟨21217750762086716205707939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14145167174724477470471959 21217750762086716205707939)
    ·
      refine ⟨31826626143130074308561909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21217750762086716205707939 31826626143130074308561909)
      ·
        refine ⟨2983746200918444466427679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31826626143130074308561909 2983746200918444466427679)
        ·
          refine ⟨4475619301377666699641519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983746200918444466427679 4475619301377666699641519)
          ·
            refine ⟨6713428952066500049462279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475619301377666699641519 6713428952066500049462279)
            ·
              refine ⟨10070143428099750074193419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713428952066500049462279 10070143428099750074193419)
              ·
                refine ⟨15105215142149625111290129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10070143428099750074193419 15105215142149625111290129)
                ·
                  refine ⟨11328911356612218833467597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15105215142149625111290129 11328911356612218833467597)
                  ·
                    refine ⟨4248341758729582062550349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11328911356612218833467597 4248341758729582062550349)
                    ·
                      refine ⟨1593128159523593273456381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4248341758729582062550349 1593128159523593273456381)
                      ·
                        rfl

theorem cell23_3102606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3102606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102606 prefixEnd_3102606 := by exact prefixLift 3102606
  have htrace : WordTrace (prefixWord ++ tailWord_3102606) baseStart_3102606 baseEnd_3102606 := by
    simpa [prefixWord, tailWord_3102606, baseEnd_3102606] using wordTrace_append hprefix tailTrace_3102606
  have hstable : (prefixWord ++ tailWord_3102606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102606).length < 2 ^ (prefixWord ++ tailWord_3102606).sum := by decide
  have hdescent : baseEnd_3102606 < baseStart_3102606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102626 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3102626 : Nat := 118140960795 + 3102626 * 2 ^ 59
def prefixEnd_3102626 : Nat := 4983230072969 + 3 ^ 40 * 3102626 * 2
def baseEnd_3102626 : Nat := 531046143045561065068763

theorem tailTrace_3102626 : CollatzResearch.WordTrace tailWord_3102626 prefixEnd_3102626 531046143045561065068763 := by
  unfold tailWord_3102626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28290516714430840794875933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75441377905148908786335821 28290516714430840794875933)
  ·
    refine ⟨10608943767911565298078475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28290516714430840794875933 10608943767911565298078475)
    ·
      refine ⟨15913415651867347947117713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10608943767911565298078475 15913415651867347947117713)
      ·
        refine ⟨11935061738900510960338285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15913415651867347947117713 11935061738900510960338285)
        ·
          refine ⟨4475648152087691610126857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11935061738900510960338285 4475648152087691610126857)
          ·
            refine ⟨3356736114065768707595143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475648152087691610126857 3356736114065768707595143)
            ·
              refine ⟨5035104171098653061392715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356736114065768707595143 5035104171098653061392715)
              ·
                refine ⟨7552656256647979592089073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035104171098653061392715 7552656256647979592089073)
                ·
                  refine ⟨5664492192485984694066805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7552656256647979592089073 5664492192485984694066805)
                  ·
                    refine ⟨531046143045561065068763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5664492192485984694066805 531046143045561065068763)
                    ·
                      rfl

theorem cell23_3102626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3102626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102626 prefixEnd_3102626 := by exact prefixLift 3102626
  have htrace : WordTrace (prefixWord ++ tailWord_3102626) baseStart_3102626 baseEnd_3102626 := by
    simpa [prefixWord, tailWord_3102626, baseEnd_3102626] using wordTrace_append hprefix tailTrace_3102626
  have hstable : (prefixWord ++ tailWord_3102626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102626).length < 2 ^ (prefixWord ++ tailWord_3102626).sum := by decide
  have hdescent : baseEnd_3102626 < baseStart_3102626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102655 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_3102655 : Nat := 118140960795 + 3102655 * 2 ^ 59
def prefixEnd_3102655 : Nat := 4983230072969 + 3 ^ 40 * 3102655 * 2
def baseEnd_3102655 : Nat := 1593153320075663581743655

theorem tailTrace_3102655 : CollatzResearch.WordTrace tailWord_3102655 prefixEnd_3102655 1593153320075663581743655 := by
  unfold tailWord_3102655
  simp only [CollatzResearch.WordTrace]
  refine ⟨113163124574618301132309419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75442083049745534088206279 113163124574618301132309419)
  ·
    refine ⟨169744686861927451698464129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113163124574618301132309419 169744686861927451698464129)
    ·
      refine ⟨127308515146445588773848097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169744686861927451698464129 127308515146445588773848097)
      ·
        refine ⟨95481386359834191580386073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127308515146445588773848097 95481386359834191580386073)
        ·
          refine ⟨71611039769875643685289555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95481386359834191580386073 71611039769875643685289555)
          ·
            refine ⟨107416559654813465527934333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71611039769875643685289555 107416559654813465527934333)
            ·
              refine ⟨40281209870555049572975375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107416559654813465527934333 40281209870555049572975375)
              ·
                refine ⟨60421814805832574359463063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40281209870555049572975375 60421814805832574359463063)
                ·
                  refine ⟨90632722208748861539194595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60421814805832574359463063 90632722208748861539194595)
                  ·
                    refine ⟨135949083313123292308791893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90632722208748861539194595 135949083313123292308791893)
                    ·
                      refine ⟨1593153320075663581743655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 135949083313123292308791893 1593153320075663581743655)
                      ·
                        rfl

theorem cell23_3102655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_3102655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102655 prefixEnd_3102655 := by exact prefixLift 3102655
  have htrace : WordTrace (prefixWord ++ tailWord_3102655) baseStart_3102655 baseEnd_3102655 := by
    simpa [prefixWord, tailWord_3102655, baseEnd_3102655] using wordTrace_append hprefix tailTrace_3102655
  have hstable : (prefixWord ++ tailWord_3102655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102655).length < 2 ^ (prefixWord ++ tailWord_3102655).sum := by decide
  have hdescent : baseEnd_3102655 < baseStart_3102655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102679 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_3102679 : Nat := 118140960795 + 3102679 * 2 ^ 59
def prefixEnd_3102679 : Nat := 4983230072969 + 3 ^ 40 * 3102679 * 2
def baseEnd_3102679 : Nat := 1593165643611371487843545

theorem tailTrace_3102679 : CollatzResearch.WordTrace tailWord_3102679 prefixEnd_3102679 1593165643611371487843545 := by
  unfold tailWord_3102679
  simp only [CollatzResearch.WordTrace]
  refine ⟨113163999926531353231183091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75442666617687568820788727 113163999926531353231183091)
  ·
    refine ⟨169745999889797029846774637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113163999926531353231183091 169745999889797029846774637)
    ·
      refine ⟨63654749958673886192540489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169745999889797029846774637 63654749958673886192540489)
      ·
        refine ⟨47741062469005414644405367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63654749958673886192540489 47741062469005414644405367)
        ·
          refine ⟨71611593703508121966608051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47741062469005414644405367 71611593703508121966608051)
          ·
            refine ⟨107417390555262182949912077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71611593703508121966608051 107417390555262182949912077)
            ·
              refine ⟨40281521458223318606217029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107417390555262182949912077 40281521458223318606217029)
              ·
                refine ⟨7552785273416872238665693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40281521458223318606217029 7552785273416872238665693)
                ·
                  refine ⟨2832294477531327089499635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7552785273416872238665693 2832294477531327089499635)
                  ·
                    refine ⟨4248441716296990634249453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2832294477531327089499635 4248441716296990634249453)
                    ·
                      refine ⟨1593165643611371487843545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4248441716296990634249453 1593165643611371487843545)
                      ·
                        rfl

theorem cell23_3102679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_3102679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102679 prefixEnd_3102679 := by exact prefixLift 3102679
  have htrace : WordTrace (prefixWord ++ tailWord_3102679) baseStart_3102679 baseEnd_3102679 := by
    simpa [prefixWord, tailWord_3102679, baseEnd_3102679] using wordTrace_append hprefix tailTrace_3102679
  have hstable : (prefixWord ++ tailWord_3102679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102679).length < 2 ^ (prefixWord ++ tailWord_3102679).sum := by decide
  have hdescent : baseEnd_3102679 < baseStart_3102679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102689 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_3102689 : Nat := 118140960795 + 3102689 * 2 ^ 59
def prefixEnd_3102689 : Nat := 4983230072969 + 3 ^ 40 * 3102689 * 2
def baseEnd_3102689 : Nat := 1593170778417916448718499

theorem tailTrace_3102689 : CollatzResearch.WordTrace tailWord_3102689 prefixEnd_3102689 1593170778417916448718499 := by
  unfold tailWord_3102689
  simp only [CollatzResearch.WordTrace]
  refine ⟨113164364656495124939047121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75442909770996749959364747 113164364656495124939047121)
  ·
    refine ⟨84873273492371343704285341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113164364656495124939047121 84873273492371343704285341)
    ·
      refine ⟨31827477559639253889107003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84873273492371343704285341 31827477559639253889107003)
      ·
        refine ⟨47741216339458880833660505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31827477559639253889107003 47741216339458880833660505)
        ·
          refine ⟨35805912254594160625245379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47741216339458880833660505 35805912254594160625245379)
          ·
            refine ⟨53708868381891240937868069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35805912254594160625245379 53708868381891240937868069)
            ·
              refine ⟨10070412821604607675850263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53708868381891240937868069 10070412821604607675850263)
              ·
                refine ⟨15105619232406911513775395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10070412821604607675850263 15105619232406911513775395)
                ·
                  refine ⟨22658428848610367270663093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15105619232406911513775395 22658428848610367270663093)
                  ·
                    refine ⟨2124227704557221931624665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22658428848610367270663093 2124227704557221931624665)
                    ·
                      refine ⟨1593170778417916448718499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124227704557221931624665 1593170778417916448718499)
                      ·
                        rfl

theorem cell23_3102689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_3102689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102689 prefixEnd_3102689 := by exact prefixLift 3102689
  have htrace : WordTrace (prefixWord ++ tailWord_3102689) baseStart_3102689 baseEnd_3102689 := by
    simpa [prefixWord, tailWord_3102689, baseEnd_3102689] using wordTrace_append hprefix tailTrace_3102689
  have hstable : (prefixWord ++ tailWord_3102689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102689).length < 2 ^ (prefixWord ++ tailWord_3102689).sum := by decide
  have hdescent : baseEnd_3102689 < baseStart_3102689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102732 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3102732 : Nat := 118140960795 + 3102732 * 2 ^ 59
def prefixEnd_3102732 : Nat := 4983230072969 + 3 ^ 40 * 3102732 * 2
def baseEnd_3102732 : Nat := 1593192858086059780480801

theorem tailTrace_3102732 : CollatzResearch.WordTrace tailWord_3102732 prefixEnd_3102732 1593192858086059780480801 := by
  unfold tailWord_3102732
  simp only [CollatzResearch.WordTrace]
  refine ⟨56582966497669671641431225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75443955330226228855241633 56582966497669671641431225)
  ·
    refine ⟨42437224873252253731073419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56582966497669671641431225 42437224873252253731073419)
    ·
      refine ⟨63655837309878380596610129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42437224873252253731073419 63655837309878380596610129)
      ·
        refine ⟨47741877982408785447457597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63655837309878380596610129 47741877982408785447457597)
        ·
          refine ⟨17903204243403294542796599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47741877982408785447457597 17903204243403294542796599)
          ·
            refine ⟨26854806365104941814194899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17903204243403294542796599 26854806365104941814194899)
            ·
              refine ⟨40282209547657412721292349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26854806365104941814194899 40282209547657412721292349)
              ·
                refine ⟨15105828580371529770484631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40282209547657412721292349 15105828580371529770484631)
                ·
                  refine ⟨22658742870557294655726947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15105828580371529770484631 22658742870557294655726947)
                  ·
                    refine ⟨33988114305835941983590421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22658742870557294655726947 33988114305835941983590421)
                    ·
                      refine ⟨1593192858086059780480801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33988114305835941983590421 1593192858086059780480801)
                      ·
                        rfl

theorem cell23_3102732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3102732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102732 prefixEnd_3102732 := by exact prefixLift 3102732
  have htrace : WordTrace (prefixWord ++ tailWord_3102732) baseStart_3102732 baseEnd_3102732 := by
    simpa [prefixWord, tailWord_3102732, baseEnd_3102732] using wordTrace_append hprefix tailTrace_3102732
  have hstable : (prefixWord ++ tailWord_3102732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102732).length < 2 ^ (prefixWord ++ tailWord_3102732).sum := by decide
  have hdescent : baseEnd_3102732 < baseStart_3102732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102749 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3102749 : Nat := 118140960795 + 3102749 * 2 ^ 59
def prefixEnd_3102749 : Nat := 4983230072969 + 3 ^ 40 * 3102749 * 2
def baseEnd_3102749 : Nat := 1593201587257186213968223

theorem tailTrace_3102749 : CollatzResearch.WordTrace tailWord_3102749 prefixEnd_3102749 1593201587257186213968223 := by
  unfold tailWord_3102749
  simp only [CollatzResearch.WordTrace]
  refine ⟨113166553036277755186231301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75444368690851836790820867 113166553036277755186231301)
  ·
    refine ⟨21218728694302079097418369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113166553036277755186231301 21218728694302079097418369)
    ·
      refine ⟨15914046520726559323063777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21218728694302079097418369 15914046520726559323063777)
      ·
        refine ⟨11935534890544919492297833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15914046520726559323063777 11935534890544919492297833)
        ·
          refine ⟨8951651167908689619223375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11935534890544919492297833 8951651167908689619223375)
          ·
            refine ⟨13427476751863034428835063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8951651167908689619223375 13427476751863034428835063)
            ·
              refine ⟨20141215127794551643252595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13427476751863034428835063 20141215127794551643252595)
              ·
                refine ⟨30211822691691827464878893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20141215127794551643252595 30211822691691827464878893)
                ·
                  refine ⟨11329433509384435299329585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30211822691691827464878893 11329433509384435299329585)
                  ·
                    refine ⟨8497075132038326474497189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11329433509384435299329585 8497075132038326474497189)
                    ·
                      refine ⟨1593201587257186213968223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8497075132038326474497189 1593201587257186213968223)
                      ·
                        rfl

theorem cell23_3102749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3102749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102749 prefixEnd_3102749 := by exact prefixLift 3102749
  have htrace : WordTrace (prefixWord ++ tailWord_3102749) baseStart_3102749 baseEnd_3102749 := by
    simpa [prefixWord, tailWord_3102749, baseEnd_3102749] using wordTrace_append hprefix tailTrace_3102749
  have hstable : (prefixWord ++ tailWord_3102749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102749).length < 2 ^ (prefixWord ++ tailWord_3102749).sum := by decide
  have hdescent : baseEnd_3102749 < baseStart_3102749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102753 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_3102753 : Nat := 118140960795 + 3102753 * 2 ^ 59
def prefixEnd_3102753 : Nat := 4983230072969 + 3 ^ 40 * 3102753 * 2
def baseEnd_3102753 : Nat := 1593203641179804198318205

theorem tailTrace_3102753 : CollatzResearch.WordTrace tailWord_3102753 prefixEnd_3102753 1593203641179804198318205 := by
  unfold tailWord_3102753
  simp only [CollatzResearch.WordTrace]
  refine ⟨113166698928263263869376913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75444465952175509246251275 113166698928263263869376913)
  ·
    refine ⟨84875024196197447902032685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113166698928263263869376913 84875024196197447902032685)
    ·
      refine ⟨31828134073574042963262257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84875024196197447902032685 31828134073574042963262257)
      ·
        refine ⟨23871100555180532222446693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31828134073574042963262257 23871100555180532222446693)
        ·
          refine ⟨4475831354096349791708755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23871100555180532222446693 4475831354096349791708755)
          ·
            refine ⟨6713747031144524687563133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475831354096349791708755 6713747031144524687563133)
            ·
              refine ⟨2517655136679196757836175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6713747031144524687563133 2517655136679196757836175)
              ·
                refine ⟨3776482705018795136754263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517655136679196757836175 3776482705018795136754263)
                ·
                  refine ⟨5664724057528192705131395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776482705018795136754263 5664724057528192705131395)
                  ·
                    refine ⟨8497086086292289057697093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664724057528192705131395 8497086086292289057697093)
                    ·
                      refine ⟨1593203641179804198318205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8497086086292289057697093 1593203641179804198318205)
                      ·
                        rfl

theorem cell23_3102753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_3102753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102753 prefixEnd_3102753 := by exact prefixLift 3102753
  have htrace : WordTrace (prefixWord ++ tailWord_3102753) baseStart_3102753 baseEnd_3102753 := by
    simpa [prefixWord, tailWord_3102753, baseEnd_3102753] using wordTrace_append hprefix tailTrace_3102753
  have hstable : (prefixWord ++ tailWord_3102753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102753).length < 2 ^ (prefixWord ++ tailWord_3102753).sum := by decide
  have hdescent : baseEnd_3102753 < baseStart_3102753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102759 : List Nat := [1, 1, 7, 1, 2, 11]
def baseStart_3102759 : Nat := 118140960795 + 3102759 * 2 ^ 59
def prefixEnd_3102759 : Nat := 4983230072969 + 3 ^ 40 * 3102759 * 2
def baseEnd_3102759 : Nat := 6556406263636753805939

theorem tailTrace_3102759 : CollatzResearch.WordTrace tailWord_3102759 prefixEnd_3102759 6556406263636753805939 := by
  unfold tailWord_3102759
  simp only [CollatzResearch.WordTrace]
  refine ⟨113166917766241526894095331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75444611844161017929396887 113166917766241526894095331)
  ·
    refine ⟨169750376649362290341142997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113166917766241526894095331 169750376649362290341142997)
    ·
      refine ⟨3978524452719428679870539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 169750376649362290341142997 3978524452719428679870539)
      ·
        refine ⟨5967786679079143019805809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978524452719428679870539 5967786679079143019805809)
        ·
          refine ⟨4475840009309357264854357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5967786679079143019805809 4475840009309357264854357)
          ·
            refine ⟨6556406263636753805939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4475840009309357264854357 6556406263636753805939)
            ·
              rfl

theorem cell23_3102759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 11].length) (baseStart_3102759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102759 prefixEnd_3102759 := by exact prefixLift 3102759
  have htrace : WordTrace (prefixWord ++ tailWord_3102759) baseStart_3102759 baseEnd_3102759 := by
    simpa [prefixWord, tailWord_3102759, baseEnd_3102759] using wordTrace_append hprefix tailTrace_3102759
  have hstable : (prefixWord ++ tailWord_3102759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102759).length < 2 ^ (prefixWord ++ tailWord_3102759).sum := by decide
  have hdescent : baseEnd_3102759 < baseStart_3102759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102770 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_3102770 : Nat := 118140960795 + 3102770 * 2 ^ 59
def prefixEnd_3102770 : Nat := 4983230072969 + 3 ^ 40 * 3102770 * 2
def baseEnd_3102770 : Nat := 1593212370350930631805627

theorem tailTrace_3102770 : CollatzResearch.WordTrace tailWord_3102770 prefixEnd_3102770 1593212370350930631805627 := by
  unfold tailWord_3102770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28291829742300418943186441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75444879312801117181830509 28291829742300418943186441)
  ·
    refine ⟨21218872306725314207389831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28291829742300418943186441 21218872306725314207389831)
    ·
      refine ⟨31828308460087971311084747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21218872306725314207389831 31828308460087971311084747)
      ·
        refine ⟨47742462690131956966627121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31828308460087971311084747 47742462690131956966627121)
        ·
          refine ⟨35806847017598967724970341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47742462690131956966627121 35806847017598967724970341)
          ·
            refine ⟨6713783815799806448431939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35806847017598967724970341 6713783815799806448431939)
            ·
              refine ⟨10070675723699709672647909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713783815799806448431939 10070675723699709672647909)
              ·
                refine ⟨1888251698193695563621483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10070675723699709672647909 1888251698193695563621483)
                ·
                  refine ⟨2832377547290543345432225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888251698193695563621483 2832377547290543345432225)
                  ·
                    refine ⟨2124283160467907509074169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832377547290543345432225 2124283160467907509074169)
                    ·
                      refine ⟨1593212370350930631805627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124283160467907509074169 1593212370350930631805627)
                      ·
                        rfl

theorem cell23_3102770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_3102770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102770 prefixEnd_3102770 := by exact prefixLift 3102770
  have htrace : WordTrace (prefixWord ++ tailWord_3102770) baseStart_3102770 baseEnd_3102770 := by
    simpa [prefixWord, tailWord_3102770, baseEnd_3102770] using wordTrace_append hprefix tailTrace_3102770
  have hstable : (prefixWord ++ tailWord_3102770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102770).length < 2 ^ (prefixWord ++ tailWord_3102770).sum := by decide
  have hdescent : baseEnd_3102770 < baseStart_3102770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102776 : List Nat := [2, 1, 2, 1, 7, 1, 1, 8]
def baseStart_3102776 : Nat := 118140960795 + 3102776 * 2 ^ 59
def prefixEnd_3102776 : Nat := 4983230072969 + 3 ^ 40 * 3102776 * 2
def baseEnd_3102776 : Nat := 59007979675365096604837

theorem tailTrace_3102776 : CollatzResearch.WordTrace tailWord_3102776 prefixEnd_3102776 59007979675365096604837 := by
  unfold tailWord_3102776
  simp only [CollatzResearch.WordTrace]
  refine ⟨56583768903589969398732091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75445025204786625864976121 56583768903589969398732091)
  ·
    refine ⟨84875653355384954098098137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56583768903589969398732091 84875653355384954098098137)
    ·
      refine ⟨63656740016538715573573603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84875653355384954098098137 63656740016538715573573603)
      ·
        refine ⟨95485110024808073360360405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63656740016538715573573603 95485110024808073360360405)
        ·
          refine ⟨2237932266206439219383447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 95485110024808073360360405 2237932266206439219383447)
          ·
            refine ⟨3356898399309658829075171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237932266206439219383447 3356898399309658829075171)
            ·
              refine ⟨5035347598964488243612757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356898399309658829075171 5035347598964488243612757)
              ·
                refine ⟨59007979675365096604837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5035347598964488243612757 59007979675365096604837)
                ·
                  rfl

theorem cell23_3102776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 8].length) (baseStart_3102776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102776 prefixEnd_3102776 := by exact prefixLift 3102776
  have htrace : WordTrace (prefixWord ++ tailWord_3102776) baseStart_3102776 baseEnd_3102776 := by
    simpa [prefixWord, tailWord_3102776, baseEnd_3102776] using wordTrace_append hprefix tailTrace_3102776
  have hstable : (prefixWord ++ tailWord_3102776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102776).length < 2 ^ (prefixWord ++ tailWord_3102776).sum := by decide
  have hdescent : baseEnd_3102776 < baseStart_3102776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102796 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3102796 : Nat := 118140960795 + 3102796 * 2 ^ 59
def prefixEnd_3102796 : Nat := 4983230072969 + 3 ^ 40 * 3102796 * 2
def baseEnd_3102796 : Nat := 1593225720847947530080507

theorem tailTrace_3102796 : CollatzResearch.WordTrace tailWord_3102796 prefixEnd_3102796 1593225720847947530080507 := by
  unfold tailWord_3102796
  simp only [CollatzResearch.WordTrace]
  refine ⟨56584133633553741106596121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75445511511404988142128161 56584133633553741106596121)
  ·
    refine ⟨42438100225165305829947091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56584133633553741106596121 42438100225165305829947091)
    ·
      refine ⟨63657150337747958744920637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42438100225165305829947091 63657150337747958744920637)
      ·
        refine ⟨23871431376655484529345239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63657150337747958744920637 23871431376655484529345239)
        ·
          refine ⟨35807147064983226794017859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23871431376655484529345239 35807147064983226794017859)
          ·
            refine ⟨53710720597474840191026789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35807147064983226794017859 53710720597474840191026789)
            ·
              refine ⟨10070760112026532535817523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53710720597474840191026789 10070760112026532535817523)
              ·
                refine ⟨15106140168039798803726285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10070760112026532535817523 15106140168039798803726285)
                ·
                  refine ⟨5664802563014924551397357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15106140168039798803726285 5664802563014924551397357)
                  ·
                    refine ⟨2124300961130596706774009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5664802563014924551397357 2124300961130596706774009)
                    ·
                      refine ⟨1593225720847947530080507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124300961130596706774009 1593225720847947530080507)
                      ·
                        rfl

theorem cell23_3102796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3102796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102796 prefixEnd_3102796 := by exact prefixLift 3102796
  have htrace : WordTrace (prefixWord ++ tailWord_3102796) baseStart_3102796 baseEnd_3102796 := by
    simpa [prefixWord, tailWord_3102796, baseEnd_3102796] using wordTrace_append hprefix tailTrace_3102796
  have hstable : (prefixWord ++ tailWord_3102796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102796).length < 2 ^ (prefixWord ++ tailWord_3102796).sum := by decide
  have hdescent : baseEnd_3102796 < baseStart_3102796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102814 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3102814 : Nat := 118140960795 + 3102814 * 2 ^ 59
def prefixEnd_3102814 : Nat := 4983230072969 + 3 ^ 40 * 3102814 * 2
def baseEnd_3102814 : Nat := 531078321166576153218475

theorem tailTrace_3102814 : CollatzResearch.WordTrace tailWord_3102814 prefixEnd_3102814 531078321166576153218475 := by
  unfold tailWord_3102814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146115472630283910918437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75445949187361514191564997 14146115472630283910918437)
  ·
    refine ⟨2652396651118178233297207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14146115472630283910918437 2652396651118178233297207)
    ·
      refine ⟨3978594976677267349945811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652396651118178233297207 3978594976677267349945811)
      ·
        refine ⟨5967892465015901024918717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978594976677267349945811 5967892465015901024918717)
        ·
          refine ⟨2237959674380962884344519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5967892465015901024918717 2237959674380962884344519)
          ·
            refine ⟨3356939511571444326516779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237959674380962884344519 3356939511571444326516779)
            ·
              refine ⟨5035409267357166489775169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356939511571444326516779 5035409267357166489775169)
              ·
                refine ⟨3776556950517874867331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035409267357166489775169 3776556950517874867331377)
                ·
                  refine ⟨2832417712888406150498533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776556950517874867331377 2832417712888406150498533)
                  ·
                    refine ⟨531078321166576153218475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832417712888406150498533 531078321166576153218475)
                    ·
                      rfl

theorem cell23_3102814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3102814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102814 prefixEnd_3102814 := by exact prefixLift 3102814
  have htrace : WordTrace (prefixWord ++ tailWord_3102814) baseStart_3102814 baseEnd_3102814 := by
    simpa [prefixWord, tailWord_3102814, baseEnd_3102814] using wordTrace_append hprefix tailTrace_3102814
  have hstable : (prefixWord ++ tailWord_3102814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102814).length < 2 ^ (prefixWord ++ tailWord_3102814).sum := by decide
  have hdescent : baseEnd_3102814 < baseStart_3102814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102839 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_3102839 : Nat := 118140960795 + 3102839 * 2 ^ 59
def prefixEnd_3102839 : Nat := 4983230072969 + 3 ^ 40 * 3102839 * 2
def baseEnd_3102839 : Nat := 1593247800516090861842809

theorem tailTrace_3102839 : CollatzResearch.WordTrace tailWord_3102839 prefixEnd_3102839 1593247800516090861842809 := by
  unfold tailWord_3102839
  simp only [CollatzResearch.WordTrace]
  refine ⟨113169835605951700557007571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75446557070634467038005047 113169835605951700557007571)
  ·
    refine ⟨169754753408927550835511357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113169835605951700557007571 169754753408927550835511357)
    ·
      refine ⟨63658032528347831563316759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169754753408927550835511357 63658032528347831563316759)
      ·
        refine ⟨95487048792521747344975139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63658032528347831563316759 95487048792521747344975139)
        ·
          refine ⟨143230573188782621017462709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95487048792521747344975139 143230573188782621017462709)
          ·
            refine ⟨13427866236448370720387129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143230573188782621017462709 13427866236448370720387129)
            ·
              refine ⟨10070899677336278040290347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13427866236448370720387129 10070899677336278040290347)
              ·
                refine ⟨15106349516004417060435521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10070899677336278040290347 15106349516004417060435521)
                ·
                  refine ⟨11329762137003312795326641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15106349516004417060435521 11329762137003312795326641)
                  ·
                    refine ⟨8497321602752484596494981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11329762137003312795326641 8497321602752484596494981)
                    ·
                      refine ⟨1593247800516090861842809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8497321602752484596494981 1593247800516090861842809)
                      ·
                        rfl

theorem cell23_3102839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_3102839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102839 prefixEnd_3102839 := by exact prefixLift 3102839
  have htrace : WordTrace (prefixWord ++ tailWord_3102839) baseStart_3102839 baseEnd_3102839 := by
    simpa [prefixWord, tailWord_3102839, baseEnd_3102839] using wordTrace_append hprefix tailTrace_3102839
  have hstable : (prefixWord ++ tailWord_3102839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102839).length < 2 ^ (prefixWord ++ tailWord_3102839).sum := by decide
  have hdescent : baseEnd_3102839 < baseStart_3102839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102842 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_3102842 : Nat := 118140960795 + 3102842 * 2 ^ 59
def prefixEnd_3102842 : Nat := 4983230072969 + 3 ^ 40 * 3102842 * 2
def baseEnd_3102842 : Nat := 1593249340958054350105295

theorem tailTrace_3102842 : CollatzResearch.WordTrace tailWord_3102842 prefixEnd_3102842 1593249340958054350105295 := by
  unfold tailWord_3102842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28292486256235208017341695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75446630016627221379577853 28292486256235208017341695)
  ·
    refine ⟨42438729384352812026012543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28292486256235208017341695 42438729384352812026012543)
    ·
      refine ⟨63658094076529218039018815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42438729384352812026012543 63658094076529218039018815)
      ·
        refine ⟨95487141114793827058528223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63658094076529218039018815 95487141114793827058528223)
        ·
          refine ⟨143230711672190740587792335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95487141114793827058528223 143230711672190740587792335)
          ·
            refine ⟨214846067508286110881688503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143230711672190740587792335 214846067508286110881688503)
            ·
              refine ⟨322269101262429166322532755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214846067508286110881688503 322269101262429166322532755)
              ·
                refine ⟨483403651893643749483799133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322269101262429166322532755 483403651893643749483799133)
                ·
                  refine ⟨181276369460116406056424675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483403651893643749483799133 181276369460116406056424675)
                  ·
                    refine ⟨271914554190174609084637013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181276369460116406056424675 271914554190174609084637013)
                    ·
                      refine ⟨1593249340958054350105295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 271914554190174609084637013 1593249340958054350105295)
                      ·
                        rfl

theorem cell23_3102842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_3102842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102842 prefixEnd_3102842 := by exact prefixLift 3102842
  have htrace : WordTrace (prefixWord ++ tailWord_3102842) baseStart_3102842 baseEnd_3102842 := by
    simpa [prefixWord, tailWord_3102842, baseEnd_3102842] using wordTrace_append hprefix tailTrace_3102842
  have hstable : (prefixWord ++ tailWord_3102842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102842).length < 2 ^ (prefixWord ++ tailWord_3102842).sum := by decide
  have hdescent : baseEnd_3102842 < baseStart_3102842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102894 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3102894 : Nat := 118140960795 + 3102894 * 2 ^ 59
def prefixEnd_3102894 : Nat := 4983230072969 + 3 ^ 40 * 3102894 * 2
def baseEnd_3102894 : Nat := 1593276041952088146655057

theorem tailTrace_3102894 : CollatzResearch.WordTrace tailWord_3102894 prefixEnd_3102894 1593276041952088146655057 := by
  unfold tailWord_3102894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146480202594055618782467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75447894413834963300173157 14146480202594055618782467)
  ·
    refine ⟨21219720303891083428173701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14146480202594055618782467 21219720303891083428173701)
    ·
      refine ⟨3978697556979578142782569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21219720303891083428173701 3978697556979578142782569)
      ·
        refine ⟨2984023167734683607086927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3978697556979578142782569 2984023167734683607086927)
        ·
          refine ⟨4476034751602025410630391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984023167734683607086927 4476034751602025410630391)
          ·
            refine ⟨6714052127403038115945587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476034751602025410630391 6714052127403038115945587)
            ·
              refine ⟨10071078191104557173918381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6714052127403038115945587 10071078191104557173918381)
              ·
                refine ⟨3776654321664208940219393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10071078191104557173918381 3776654321664208940219393)
                ·
                  refine ⟨2832490741248156705164545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776654321664208940219393 2832490741248156705164545)
                  ·
                    refine ⟨2124368055936117528873409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832490741248156705164545 2124368055936117528873409)
                    ·
                      refine ⟨1593276041952088146655057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124368055936117528873409 1593276041952088146655057)
                      ·
                        rfl

theorem cell23_3102894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3102894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102894 prefixEnd_3102894 := by exact prefixLift 3102894
  have htrace : WordTrace (prefixWord ++ tailWord_3102894) baseStart_3102894 baseEnd_3102894 := by
    simpa [prefixWord, tailWord_3102894, baseEnd_3102894] using wordTrace_append hprefix tailTrace_3102894
  have hstable : (prefixWord ++ tailWord_3102894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102894).length < 2 ^ (prefixWord ++ tailWord_3102894).sum := by decide
  have hdescent : baseEnd_3102894 < baseStart_3102894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102899 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 4]
def baseStart_3102899 : Nat := 118140960795 + 3102899 * 2 ^ 59
def prefixEnd_3102899 : Nat := 4983230072969 + 3 ^ 40 * 3102899 * 2
def baseEnd_3102899 : Nat := 1593278609355360627092533

theorem tailTrace_3102899 : CollatzResearch.WordTrace tailWord_3102899 prefixEnd_3102899 1593278609355360627092533 := by
  unfold tailWord_3102899
  simp only [CollatzResearch.WordTrace]
  refine ⟨113172023985734330804191751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75448015990489553869461167 113172023985734330804191751)
  ·
    refine ⟨169758035978601496206287627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113172023985734330804191751 169758035978601496206287627)
    ·
      refine ⟨254637053967902244309431441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169758035978601496206287627 254637053967902244309431441)
      ·
        refine ⟨190977790475926683232073581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254637053967902244309431441 190977790475926683232073581)
        ·
          refine ⟨71616671428472506212027593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190977790475926683232073581 71616671428472506212027593)
          ·
            refine ⟨53712503571354379659020695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71616671428472506212027593 53712503571354379659020695)
            ·
              refine ⟨80568755357031569488531043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53712503571354379659020695 80568755357031569488531043)
              ·
                refine ⟨120853133035547354232796565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80568755357031569488531043 120853133035547354232796565)
                ·
                  refine ⟨5664990611041282229662339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120853133035547354232796565 5664990611041282229662339)
                  ·
                    refine ⟨8497485916561923344493509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664990611041282229662339 8497485916561923344493509)
                    ·
                      refine ⟨1593278609355360627092533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8497485916561923344493509 1593278609355360627092533)
                      ·
                        rfl

theorem cell23_3102899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_3102899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102899 prefixEnd_3102899 := by exact prefixLift 3102899
  have htrace : WordTrace (prefixWord ++ tailWord_3102899) baseStart_3102899 baseEnd_3102899 := by
    simpa [prefixWord, tailWord_3102899, baseEnd_3102899] using wordTrace_append hprefix tailTrace_3102899
  have hstable : (prefixWord ++ tailWord_3102899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102899).length < 2 ^ (prefixWord ++ tailWord_3102899).sum := by decide
  have hdescent : baseEnd_3102899 < baseStart_3102899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102939 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 6]
def baseStart_3102939 : Nat := 118140960795 + 3102939 * 2 ^ 59
def prefixEnd_3102939 : Nat := 4983230072969 + 3 ^ 40 * 3102939 * 2
def baseEnd_3102939 : Nat := 177033238731282274510261

theorem tailTrace_3102939 : CollatzResearch.WordTrace tailWord_3102939 prefixEnd_3102939 177033238731282274510261 := by
  unfold tailWord_3102939
  simp only [CollatzResearch.WordTrace]
  refine ⟨113173482905589417635647871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75448988603726278423765247 113173482905589417635647871)
  ·
    refine ⟨169760224358384126453471807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113173482905589417635647871 169760224358384126453471807)
    ·
      refine ⟨254640336537576189680207711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169760224358384126453471807 254640336537576189680207711)
      ·
        refine ⟨381960504806364284520311567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254640336537576189680207711 381960504806364284520311567)
        ·
          refine ⟨572940757209546426780467351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381960504806364284520311567 572940757209546426780467351)
          ·
            refine ⟨859411135814319640170701027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572940757209546426780467351 859411135814319640170701027)
            ·
              refine ⟨1289116703721479460256051541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859411135814319640170701027 1289116703721479460256051541)
              ·
                refine ⟨3776709092934021856218901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1289116703721479460256051541 3776709092934021856218901)
                ·
                  refine ⟨177033238731282274510261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3776709092934021856218901 177033238731282274510261)
                  ·
                    rfl

theorem cell23_3102939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 6].length) (baseStart_3102939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3102939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3102939 prefixEnd_3102939 := by exact prefixLift 3102939
  have htrace : WordTrace (prefixWord ++ tailWord_3102939) baseStart_3102939 baseEnd_3102939 := by
    simpa [prefixWord, tailWord_3102939, baseEnd_3102939] using wordTrace_append hprefix tailTrace_3102939
  have hstable : (prefixWord ++ tailWord_3102939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102939).length < 2 ^ (prefixWord ++ tailWord_3102939).sum := by decide
  have hdescent : baseEnd_3102939 < baseStart_3102939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103000 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3103000 : Nat := 118140960795 + 3103000 * 2 ^ 59
def prefixEnd_3103000 : Nat := 4983230072969 + 3 ^ 40 * 3103000 * 2
def baseEnd_3103000 : Nat := 1593330470901464731929569

theorem tailTrace_3103000 : CollatzResearch.WordTrace tailWord_3103000 prefixEnd_3103000 1593330470901464731929569 := by
  unfold tailWord_3103000
  simp only [CollatzResearch.WordTrace]
  refine ⟨56587853879184212526809227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75450471838912283369078969 56587853879184212526809227)
  ·
    refine ⟨84881780818776318790213841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56587853879184212526809227 84881780818776318790213841)
    ·
      refine ⟨63661335614082239092660381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84881780818776318790213841 63661335614082239092660381)
      ·
        refine ⟨23873000855280839659747643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63661335614082239092660381 23873000855280839659747643)
        ·
          refine ⟨35809501282921259489621465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23873000855280839659747643 35809501282921259489621465)
          ·
            refine ⟨26857125962190944617216099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35809501282921259489621465 26857125962190944617216099)
            ·
              refine ⟨40285688943286416925824149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26857125962190944617216099 40285688943286416925824149)
              ·
                refine ⟨1888391669216550793398007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40285688943286416925824149 1888391669216550793398007)
                ·
                  refine ⟨2832587503824826190097011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888391669216550793398007 2832587503824826190097011)
                  ·
                    refine ⟨4248881255737239285145517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2832587503824826190097011 4248881255737239285145517)
                    ·
                      refine ⟨1593330470901464731929569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4248881255737239285145517 1593330470901464731929569)
                      ·
                        rfl

theorem cell23_3103000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3103000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103000 prefixEnd_3103000 := by exact prefixLift 3103000
  have htrace : WordTrace (prefixWord ++ tailWord_3103000) baseStart_3103000 baseEnd_3103000 := by
    simpa [prefixWord, tailWord_3103000, baseEnd_3103000] using wordTrace_append hprefix tailTrace_3103000
  have hstable : (prefixWord ++ tailWord_3103000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103000).length < 2 ^ (prefixWord ++ tailWord_3103000).sum := by decide
  have hdescent : baseEnd_3103000 < baseStart_3103000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103033 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 4, 4]
def baseStart_3103033 : Nat := 118140960795 + 3103033 * 2 ^ 59
def prefixEnd_3103033 : Nat := 4983230072969 + 3 ^ 40 * 3103033 * 2
def baseEnd_3103033 : Nat := 531115805254354367605639

theorem tailTrace_3103033 : CollatzResearch.WordTrace tailWord_3103033 prefixEnd_3103033 531115805254354367605639 := by
  unfold tailWord_3103033
  simp only [CollatzResearch.WordTrace]
  refine ⟨113176911367248871689569753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75451274244832581126379835 113176911367248871689569753)
  ·
    refine ⟨84882683525436653767177315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113176911367248871689569753 84882683525436653767177315)
    ·
      refine ⟨127324025288154980650765973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84882683525436653767177315 127324025288154980650765973)
      ·
        refine ⟨5968313685382264718004655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127324025288154980650765973 5968313685382264718004655)
        ·
          refine ⟨8952470528073397077006983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5968313685382264718004655 8952470528073397077006983)
          ·
            refine ⟨13428705792110095615510475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952470528073397077006983 13428705792110095615510475)
            ·
              refine ⟨20143058688165143423265713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13428705792110095615510475 20143058688165143423265713)
              ·
                refine ⟨15107294016123857567449285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20143058688165143423265713 15107294016123857567449285)
                ·
                  refine ⟨2832617628023223293896741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15107294016123857567449285 2832617628023223293896741)
                  ·
                    refine ⟨531115805254354367605639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832617628023223293896741 531115805254354367605639)
                    ·
                      rfl

theorem cell23_3103033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_3103033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103033 prefixEnd_3103033 := by exact prefixLift 3103033
  have htrace : WordTrace (prefixWord ++ tailWord_3103033) baseStart_3103033 baseEnd_3103033 := by
    simpa [prefixWord, tailWord_3103033, baseEnd_3103033] using wordTrace_append hprefix tailTrace_3103033
  have hstable : (prefixWord ++ tailWord_3103033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103033).length < 2 ^ (prefixWord ++ tailWord_3103033).sum := by decide
  have hdescent : baseEnd_3103033 < baseStart_3103033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103036 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3103036 : Nat := 118140960795 + 3103036 * 2 ^ 59
def prefixEnd_3103036 : Nat := 4983230072969 + 3 ^ 40 * 3103036 * 2
def baseEnd_3103036 : Nat := 1593348956205026591079403

theorem tailTrace_3103036 : CollatzResearch.WordTrace tailWord_3103036 prefixEnd_3103036 1593348956205026591079403 := by
  unfold tailWord_3103036
  simp only [CollatzResearch.WordTrace]
  refine ⟨56588510393119001600964481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75451347190825335467952641 56588510393119001600964481)
  ·
    refine ⟨42441382794839251200723361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56588510393119001600964481 42441382794839251200723361)
    ·
      refine ⟨31831037096129438400542521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42441382794839251200723361 31831037096129438400542521)
      ·
        refine ⟨23873277822097078800406891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31831037096129438400542521 23873277822097078800406891)
        ·
          refine ⟨35809916733145618200610337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23873277822097078800406891 35809916733145618200610337)
          ·
            refine ⟨26857437549859213650457753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35809916733145618200610337 26857437549859213650457753)
            ·
              refine ⟨20143078162394410237843315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26857437549859213650457753 20143078162394410237843315)
              ·
                refine ⟨30214617243591615356764973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20143078162394410237843315 30214617243591615356764973)
                ·
                  refine ⟨11330481466346855758786865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30214617243591615356764973 11330481466346855758786865)
                  ·
                    refine ⟨8497861099760141819090149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11330481466346855758786865 8497861099760141819090149)
                    ·
                      refine ⟨1593348956205026591079403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8497861099760141819090149 1593348956205026591079403)
                      ·
                        rfl

theorem cell23_3103036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3103036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103036 prefixEnd_3103036 := by exact prefixLift 3103036
  have htrace : WordTrace (prefixWord ++ tailWord_3103036) baseStart_3103036 baseEnd_3103036 := by
    simpa [prefixWord, tailWord_3103036, baseEnd_3103036] using wordTrace_append hprefix tailTrace_3103036
  have hstable : (prefixWord ++ tailWord_3103036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103036).length < 2 ^ (prefixWord ++ tailWord_3103036).sum := by decide
  have hdescent : baseEnd_3103036 < baseStart_3103036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103043 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 3]
def baseStart_3103043 : Nat := 118140960795 + 3103043 * 2 ^ 59
def prefixEnd_3103043 : Nat := 4983230072969 + 3 ^ 40 * 3103043 * 2
def baseEnd_3103043 : Nat := 1593352550569608063691871

theorem tailTrace_3103043 : CollatzResearch.WordTrace tailWord_3103043 prefixEnd_3103043 1593352550569608063691871 := by
  unfold tailWord_3103043
  simp only [CollatzResearch.WordTrace]
  refine ⟨113177276097212643397433783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75451517398141762264955855 113177276097212643397433783)
  ·
    refine ⟨169765914145818965096150675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113177276097212643397433783 169765914145818965096150675)
    ·
      refine ⟨254648871218728447644226013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169765914145818965096150675 254648871218728447644226013)
      ·
        refine ⟨95493326707023167866584755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254648871218728447644226013 95493326707023167866584755)
        ·
          refine ⟨143239990060534751799877133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95493326707023167866584755 143239990060534751799877133)
          ·
            refine ⟨53714996272700531924953925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143239990060534751799877133 53714996272700531924953925)
            ·
              refine ⟨10071561801131349735928861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53714996272700531924953925 10071561801131349735928861)
              ·
                refine ⟨3776835675424256150973323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10071561801131349735928861 3776835675424256150973323)
                ·
                  refine ⟨5665253513136384226459985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776835675424256150973323 5665253513136384226459985)
                  ·
                    refine ⟨4248940134852288169844989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5665253513136384226459985 4248940134852288169844989)
                    ·
                      refine ⟨1593352550569608063691871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4248940134852288169844989 1593352550569608063691871)
                      ·
                        rfl

theorem cell23_3103043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_3103043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103043 prefixEnd_3103043 := by exact prefixLift 3103043
  have htrace : WordTrace (prefixWord ++ tailWord_3103043) baseStart_3103043 baseEnd_3103043 := by
    simpa [prefixWord, tailWord_3103043, baseEnd_3103043] using wordTrace_append hprefix tailTrace_3103043
  have hstable : (prefixWord ++ tailWord_3103043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103043).length < 2 ^ (prefixWord ++ tailWord_3103043).sum := by decide
  have hdescent : baseEnd_3103043 < baseStart_3103043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103057 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 3, 2, 2]
def baseStart_3103057 : Nat := 118140960795 + 3103057 * 2 ^ 59
def prefixEnd_3103057 : Nat := 4983230072969 + 3 ^ 40 * 3103057 * 2
def baseEnd_3103057 : Nat := 1593359739298771008916807

theorem tailTrace_3103057 : CollatzResearch.WordTrace tailWord_3103057 prefixEnd_3103057 1593359739298771008916807 := by
  unfold tailWord_3103057
  simp only [CollatzResearch.WordTrace]
  refine ⟨113177786719161923788443425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75451857812774615858962283 113177786719161923788443425)
  ·
    refine ⟨84883340039371442841332569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113177786719161923788443425 84883340039371442841332569)
    ·
      refine ⟨63662505029528582130999427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84883340039371442841332569 63662505029528582130999427)
      ·
        refine ⟨95493757544292873196499141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63662505029528582130999427 95493757544292873196499141)
        ·
          refine ⟨17905079539554913724343589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95493757544292873196499141 17905079539554913724343589)
          ·
            refine ⟨3357202413666546323314423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17905079539554913724343589 3357202413666546323314423)
            ·
              refine ⟨5035803620499819484971635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357202413666546323314423 5035803620499819484971635)
              ·
                refine ⟨7553705430749729227457453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035803620499819484971635 7553705430749729227457453)
                ·
                  refine ⟨2832639536531148460296545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7553705430749729227457453 2832639536531148460296545)
                  ·
                    refine ⟨2124479652398361345222409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2832639536531148460296545 2124479652398361345222409)
                    ·
                      refine ⟨1593359739298771008916807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124479652398361345222409 1593359739298771008916807)
                      ·
                        rfl

theorem cell23_3103057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_3103057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103057 prefixEnd_3103057 := by exact prefixLift 3103057
  have htrace : WordTrace (prefixWord ++ tailWord_3103057) baseStart_3103057 baseEnd_3103057 := by
    simpa [prefixWord, tailWord_3103057, baseEnd_3103057] using wordTrace_append hprefix tailTrace_3103057
  have hstable : (prefixWord ++ tailWord_3103057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103057).length < 2 ^ (prefixWord ++ tailWord_3103057).sum := by decide
  have hdescent : baseEnd_3103057 < baseStart_3103057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103083 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 3, 3, 2]
def baseStart_3103083 : Nat := 118140960795 + 3103083 * 2 ^ 59
def prefixEnd_3103083 : Nat := 4983230072969 + 3 ^ 40 * 3103083 * 2
def baseEnd_3103083 : Nat := 1593373089795787907191687

theorem tailTrace_3103083 : CollatzResearch.WordTrace tailWord_3103083 prefixEnd_3103083 1593373089795787907191687 := by
  unfold tailWord_3103083
  simp only [CollatzResearch.WordTrace]
  refine ⟨113178735017067730228889903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75452490011378486819259935 113178735017067730228889903)
  ·
    refine ⟨169768102525601595343334855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113178735017067730228889903 169768102525601595343334855)
    ·
      refine ⟨254652153788402393015002283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169768102525601595343334855 254652153788402393015002283)
      ·
        refine ⟨381978230682603589522503425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254652153788402393015002283 381978230682603589522503425)
        ·
          refine ⟨286483673011952692141877569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381978230682603589522503425 286483673011952692141877569)
          ·
            refine ⟨214862754758964519106408177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286483673011952692141877569 214862754758964519106408177)
            ·
              refine ⟨161147066069223389329806133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214862754758964519106408177 161147066069223389329806133)
              ·
                refine ⟨15107537443989692749669325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161147066069223389329806133 15107537443989692749669325)
                ·
                  refine ⟨5665326541496134781125997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15107537443989692749669325 5665326541496134781125997)
                  ·
                    refine ⟨2124497453061050542922249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5665326541496134781125997 2124497453061050542922249)
                    ·
                      refine ⟨1593373089795787907191687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2124497453061050542922249 1593373089795787907191687)
                      ·
                        rfl

theorem cell23_3103083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3, 2].length) (baseStart_3103083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3103083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3103083 prefixEnd_3103083 := by exact prefixLift 3103083
  have htrace : WordTrace (prefixWord ++ tailWord_3103083) baseStart_3103083 baseEnd_3103083 := by
    simpa [prefixWord, tailWord_3103083, baseEnd_3103083] using wordTrace_append hprefix tailTrace_3103083
  have hstable : (prefixWord ++ tailWord_3103083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103083).length < 2 ^ (prefixWord ++ tailWord_3103083).sum := by decide
  have hdescent : baseEnd_3103083 < baseStart_3103083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
