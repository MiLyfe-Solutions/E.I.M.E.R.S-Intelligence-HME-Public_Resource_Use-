import V185TrunkScan20Chunk128

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_784719 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 2]
def baseStart_784719 : Nat := 118140960795 + 784719 * 2 ^ 59
def prefixEnd_784719 : Nat := 4983230072969 + 3 ^ 40 * 784719 * 2
def baseEnd_784719 : Nat := 358167133969440459558799

theorem tailTrace_784719 : CollatzResearch.WordTrace tailWord_784719 prefixEnd_784719 358167133969440459558799 := by
  unfold tailWord_784719
  simp only [CollatzResearch.WordTrace]
  refine ⟨28621053244104557180485211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19080702162736371453656807 28621053244104557180485211)
  ·
    refine ⟨42931579866156835770727817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28621053244104557180485211 42931579866156835770727817)
    ·
      refine ⟨32198684899617626828045863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42931579866156835770727817 32198684899617626828045863)
      ·
        refine ⟨48298027349426440242068795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32198684899617626828045863 48298027349426440242068795)
        ·
          refine ⟨72447041024139660363103193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48298027349426440242068795 72447041024139660363103193)
          ·
            refine ⟨54335280768104745272327395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72447041024139660363103193 54335280768104745272327395)
            ·
              refine ⟨81502921152157117908491093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54335280768104745272327395 81502921152157117908491093)
              ·
                refine ⟨477556178625920612745065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 81502921152157117908491093 477556178625920612745065)
                ·
                  refine ⟨358167133969440459558799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477556178625920612745065 358167133969440459558799)
                  ·
                    rfl

theorem cell20_784719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 2].length) (baseStart_784719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784719 prefixEnd_784719 := by exact prefixLift 784719
  have htrace : WordTrace (prefixWord ++ tailWord_784719) baseStart_784719 baseEnd_784719 := by
    simpa [prefixWord, tailWord_784719, baseEnd_784719] using wordTrace_append hprefix tailTrace_784719
  have hstable : (prefixWord ++ tailWord_784719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784719).length < 2 ^ (prefixWord ++ tailWord_784719).sum := by decide
  have hdescent : baseEnd_784719 < baseStart_784719 := by decide
  rcases family_descends (prefixWord ++ tailWord_784719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784732 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 4]
def baseStart_784732 : Nat := 118140960795 + 784732 * 2 ^ 59
def prefixEnd_784732 : Nat := 4983230072969 + 3 ^ 40 * 784732 * 2
def baseEnd_784732 : Nat := 358173067523670192125413

theorem tailTrace_784732 : CollatzResearch.WordTrace tailWord_784732 prefixEnd_784732 358173067523670192125413 := by
  unfold tailWord_784732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310763696528730200354225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19081018262038306933805633 14310763696528730200354225)
  ·
    refine ⟨10733072772396547650265669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14310763696528730200354225 10733072772396547650265669)
    ·
      refine ⟨2012451144824352684424813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10733072772396547650265669 2012451144824352684424813)
      ·
        refine ⟨754669179309132256659305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2012451144824352684424813 754669179309132256659305)
        ·
          refine ⟨566001884481849192494479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754669179309132256659305 566001884481849192494479)
          ·
            refine ⟨849002826722773788741719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566001884481849192494479 849002826722773788741719)
            ·
              refine ⟨1273504240084160683112579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849002826722773788741719 1273504240084160683112579)
              ·
                refine ⟨1910256360126241024668869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273504240084160683112579 1910256360126241024668869)
                ·
                  refine ⟨358173067523670192125413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1910256360126241024668869 358173067523670192125413)
                  ·
                    rfl

theorem cell20_784732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_784732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784732 prefixEnd_784732 := by exact prefixLift 784732
  have htrace : WordTrace (prefixWord ++ tailWord_784732) baseStart_784732 baseEnd_784732 := by
    simpa [prefixWord, tailWord_784732, baseEnd_784732] using wordTrace_append hprefix tailTrace_784732
  have hstable : (prefixWord ++ tailWord_784732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784732).length < 2 ^ (prefixWord ++ tailWord_784732).sum := by decide
  have hdescent : baseEnd_784732 < baseStart_784732 := by decide
  rcases family_descends (prefixWord ++ tailWord_784732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784736 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_784736 : Nat := 118140960795 + 784736 * 2 ^ 59
def prefixEnd_784736 : Nat := 4983230072969 + 3 ^ 40 * 784736 * 2
def baseEnd_784736 : Nat := 358174893232663955992063

theorem tailTrace_784736 : CollatzResearch.WordTrace tailWord_784736 prefixEnd_784736 358174893232663955992063 := by
  unfold tailWord_784736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310836642521484541927031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19081115523361979389236041 14310836642521484541927031)
  ·
    refine ⟨21466254963782226812890547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14310836642521484541927031 21466254963782226812890547)
    ·
      refine ⟨32199382445673340219335821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21466254963782226812890547 32199382445673340219335821)
      ·
        refine ⟨12074768417127502582250933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32199382445673340219335821 12074768417127502582250933)
        ·
          refine ⟨1132009539105703367086025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12074768417127502582250933 1132009539105703367086025)
          ·
            refine ⟨849007154329277525314519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132009539105703367086025 849007154329277525314519)
            ·
              refine ⟨1273510731493916287971779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849007154329277525314519 1273510731493916287971779)
              ·
                refine ⟨1910266097240874431957669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273510731493916287971779 1910266097240874431957669)
                ·
                  refine ⟨358174893232663955992063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1910266097240874431957669 358174893232663955992063)
                  ·
                    rfl

theorem cell20_784736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_784736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784736 prefixEnd_784736 := by exact prefixLift 784736
  have htrace : WordTrace (prefixWord ++ tailWord_784736) baseStart_784736 baseEnd_784736 := by
    simpa [prefixWord, tailWord_784736, baseEnd_784736] using wordTrace_append hprefix tailTrace_784736
  have hstable : (prefixWord ++ tailWord_784736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784736).length < 2 ^ (prefixWord ++ tailWord_784736).sum := by decide
  have hdescent : baseEnd_784736 < baseStart_784736 := by decide
  rcases family_descends (prefixWord ++ tailWord_784736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784746 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_784746 : Nat := 118140960795 + 784746 * 2 ^ 59
def prefixEnd_784746 : Nat := 4983230072969 + 3 ^ 40 * 784746 * 2
def baseEnd_784746 : Nat := 358179457505148365658689

theorem tailTrace_784746 : CollatzResearch.WordTrace tailWord_784746 prefixEnd_784746 358179457505148365658689 := by
  unfold tailWord_784746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7155509503751685197929523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19081358676671160527812061 7155509503751685197929523)
  ·
    refine ⟨10733264255627527796894285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7155509503751685197929523 10733264255627527796894285)
    ·
      refine ⟨4024974095860322923835357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10733264255627527796894285 4024974095860322923835357)
      ·
        refine ⟨1509365285947621096438259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4024974095860322923835357 1509365285947621096438259)
        ·
          refine ⟨2264047928921431644657389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509365285947621096438259 2264047928921431644657389)
          ·
            refine ⟨849017973345536866746521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2264047928921431644657389 849017973345536866746521)
            ·
              refine ⟨636763480009152650059891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849017973345536866746521 636763480009152650059891)
              ·
                refine ⟨955145220013728975089837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636763480009152650059891 955145220013728975089837)
                ·
                  refine ⟨358179457505148365658689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955145220013728975089837 358179457505148365658689)
                  ·
                    rfl

theorem cell20_784746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_784746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784746 prefixEnd_784746 := by exact prefixLift 784746
  have htrace : WordTrace (prefixWord ++ tailWord_784746) baseStart_784746 baseEnd_784746 := by
    simpa [prefixWord, tailWord_784746, baseEnd_784746] using wordTrace_append hprefix tailTrace_784746
  have hstable : (prefixWord ++ tailWord_784746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784746).length < 2 ^ (prefixWord ++ tailWord_784746).sum := by decide
  have hdescent : baseEnd_784746 < baseStart_784746 := by decide
  rcases family_descends (prefixWord ++ tailWord_784746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784798 : List Nat := [4, 3, 1, 2, 1, 3, 1, 5]
def baseStart_784798 : Nat := 118140960795 + 784798 * 2 ^ 59
def prefixEnd_784798 : Nat := 4983230072969 + 3 ^ 40 * 784798 * 2
def baseEnd_784798 : Nat := 119401063907355765308381

theorem tailTrace_784798 : CollatzResearch.WordTrace tailWord_784798 prefixEnd_784798 119401063907355765308381 := by
  unfold tailWord_784798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577991826352294209076381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19082623073878902448407365 3577991826352294209076381)
  ·
    refine ⟨1341746934882110328403643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3577991826352294209076381 1341746934882110328403643)
    ·
      refine ⟨2012620402323165492605465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341746934882110328403643 2012620402323165492605465)
      ·
        refine ⟨1509465301742374119454099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2012620402323165492605465 1509465301742374119454099)
        ·
          refine ⟨2264197952613561179181149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509465301742374119454099 2264197952613561179181149)
          ·
            refine ⟨849074232230085442192931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2264197952613561179181149 849074232230085442192931)
            ·
              refine ⟨1273611348345128163289397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849074232230085442192931 1273611348345128163289397)
              ·
                refine ⟨119401063907355765308381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1273611348345128163289397 119401063907355765308381)
                ·
                  rfl

theorem cell20_784798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_784798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784798 prefixEnd_784798 := by exact prefixLift 784798
  have htrace : WordTrace (prefixWord ++ tailWord_784798) baseStart_784798 baseEnd_784798 := by
    simpa [prefixWord, tailWord_784798, baseEnd_784798] using wordTrace_append hprefix tailTrace_784798
  have hstable : (prefixWord ++ tailWord_784798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784798).length < 2 ^ (prefixWord ++ tailWord_784798).sum := by decide
  have hdescent : baseEnd_784798 < baseStart_784798 := by decide
  rcases family_descends (prefixWord ++ tailWord_784798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784864 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_784864 : Nat := 118140960795 + 784864 * 2 ^ 59
def prefixEnd_784864 : Nat := 4983230072969 + 3 ^ 40 * 784864 * 2
def baseEnd_784864 : Nat := 358233315920464399724873

theorem tailTrace_784864 : CollatzResearch.WordTrace tailWord_784864 prefixEnd_784864 358233315920464399724873 := by
  unfold tailWord_784864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14313170914289623472256823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19084227885719497963009097 14313170914289623472256823)
  ·
    refine ⟨21469756371434435208385235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14313170914289623472256823 21469756371434435208385235)
    ·
      refine ⟨32204634557151652812577853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21469756371434435208385235 32204634557151652812577853)
      ·
        refine ⟨12076737958931869804716695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32204634557151652812577853 12076737958931869804716695)
        ·
          refine ⟨18115106938397804707075043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12076737958931869804716695 18115106938397804707075043)
          ·
            refine ⟨27172660407596707060612565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18115106938397804707075043 27172660407596707060612565)
            ·
              refine ⟨636859228303047821733107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27172660407596707060612565 636859228303047821733107)
              ·
                refine ⟨955288842454571732599661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636859228303047821733107 955288842454571732599661)
                ·
                  refine ⟨358233315920464399724873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955288842454571732599661 358233315920464399724873)
                  ·
                    rfl

theorem cell20_784864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_784864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784864 prefixEnd_784864 := by exact prefixLift 784864
  have htrace : WordTrace (prefixWord ++ tailWord_784864) baseStart_784864 baseEnd_784864 := by
    simpa [prefixWord, tailWord_784864, baseEnd_784864] using wordTrace_append hprefix tailTrace_784864
  have hstable : (prefixWord ++ tailWord_784864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784864).length < 2 ^ (prefixWord ++ tailWord_784864).sum := by decide
  have hdescent : baseEnd_784864 < baseStart_784864 := by decide
  rcases family_descends (prefixWord ++ tailWord_784864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784878 : List Nat := [4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_784878 : Nat := 118140960795 + 784878 * 2 ^ 59
def prefixEnd_784878 : Nat := 4983230072969 + 3 ^ 40 * 784878 * 2
def baseEnd_784878 : Nat := 119413235300647524419383

theorem tailTrace_784878 : CollatzResearch.WordTrace tailWord_784878 prefixEnd_784878 119413235300647524419383 := by
  unfold tailWord_784878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578356556316065916940411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19084568300352351557015525 3578356556316065916940411)
  ·
    refine ⟨5367534834474098875410617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578356556316065916940411 5367534834474098875410617)
    ·
      refine ⟨4025651125855574156557963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5367534834474098875410617 4025651125855574156557963)
      ·
        refine ⟨6038476688783361234836945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025651125855574156557963 6038476688783361234836945)
        ·
          refine ⟨4528857516587520926127709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6038476688783361234836945 4528857516587520926127709)
          ·
            refine ⟨1698321568720320347297891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4528857516587520926127709 1698321568720320347297891)
            ·
              refine ⟨2547482353080480520946837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698321568720320347297891 2547482353080480520946837)
              ·
                refine ⟨119413235300647524419383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2547482353080480520946837 119413235300647524419383)
                ·
                  rfl

theorem cell20_784878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_784878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784878 prefixEnd_784878 := by exact prefixLift 784878
  have htrace : WordTrace (prefixWord ++ tailWord_784878) baseStart_784878 baseEnd_784878 := by
    simpa [prefixWord, tailWord_784878, baseEnd_784878] using wordTrace_append hprefix tailTrace_784878
  have hstable : (prefixWord ++ tailWord_784878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784878).length < 2 ^ (prefixWord ++ tailWord_784878).sum := by decide
  have hdescent : baseEnd_784878 < baseStart_784878 := by decide
  rcases family_descends (prefixWord ++ tailWord_784878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784919 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 3]
def baseStart_784919 : Nat := 118140960795 + 784919 * 2 ^ 59
def prefixEnd_784919 : Nat := 4983230072969 + 3 ^ 40 * 784919 * 2
def baseEnd_784919 : Nat := 358258419419128652891315

theorem tailTrace_784919 : CollatzResearch.WordTrace tailWord_784919 prefixEnd_784919 358258419419128652891315 := by
  unfold tailWord_784919
  simp only [CollatzResearch.WordTrace]
  refine ⟨28628347843379991337765811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19085565228919994225177207 28628347843379991337765811)
  ·
    refine ⟨42942521765069987006648717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28628347843379991337765811 42942521765069987006648717)
    ·
      refine ⟨16103445661901245127493269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42942521765069987006648717 16103445661901245127493269)
      ·
        refine ⟨754849015401620865351247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16103445661901245127493269 754849015401620865351247)
        ·
          refine ⟨1132273523102431298026871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754849015401620865351247 1132273523102431298026871)
          ·
            refine ⟨1698410284653646947040307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132273523102431298026871 1698410284653646947040307)
            ·
              refine ⟨2547615426980470420560461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698410284653646947040307 2547615426980470420560461)
              ·
                refine ⟨955355785117676407710173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2547615426980470420560461 955355785117676407710173)
                ·
                  refine ⟨358258419419128652891315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955355785117676407710173 358258419419128652891315)
                  ·
                    rfl

theorem cell20_784919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_784919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784919 prefixEnd_784919 := by exact prefixLift 784919
  have htrace : WordTrace (prefixWord ++ tailWord_784919) baseStart_784919 baseEnd_784919 := by
    simpa [prefixWord, tailWord_784919, baseEnd_784919] using wordTrace_append hprefix tailTrace_784919
  have hstable : (prefixWord ++ tailWord_784919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784919).length < 2 ^ (prefixWord ++ tailWord_784919).sum := by decide
  have hdescent : baseEnd_784919 < baseStart_784919 := by decide
  rcases family_descends (prefixWord ++ tailWord_784919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784930 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_784930 : Nat := 118140960795 + 784930 * 2 ^ 59
def prefixEnd_784930 : Nat := 4983230072969 + 3 ^ 40 * 784930 * 2
def baseEnd_784930 : Nat := 358263440118861503524603

theorem tailTrace_784930 : CollatzResearch.WordTrace tailWord_784930 prefixEnd_784930 358263440118861503524603 := by
  unfold tailWord_784930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157187261585035054104061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19085832697560093477610829 7157187261585035054104061)
  ·
    refine ⟨2683945223094388145289023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7157187261585035054104061 2683945223094388145289023)
    ·
      refine ⟨4025917834641582217933535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683945223094388145289023 4025917834641582217933535)
      ·
        refine ⟨6038876751962373326900303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025917834641582217933535 6038876751962373326900303)
        ·
          refine ⟨9058315127943559990350455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038876751962373326900303 9058315127943559990350455)
          ·
            refine ⟨13587472691915339985525683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058315127943559990350455 13587472691915339985525683)
            ·
              refine ⟨20381209037873009978288525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13587472691915339985525683 20381209037873009978288525)
              ·
                refine ⟨7642953389202378741858197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20381209037873009978288525 7642953389202378741858197)
                ·
                  refine ⟨358263440118861503524603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7642953389202378741858197 358263440118861503524603)
                  ·
                    rfl

theorem cell20_784930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_784930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784930 prefixEnd_784930 := by exact prefixLift 784930
  have htrace : WordTrace (prefixWord ++ tailWord_784930) baseStart_784930 baseEnd_784930 := by
    simpa [prefixWord, tailWord_784930, baseEnd_784930] using wordTrace_append hprefix tailTrace_784930
  have hstable : (prefixWord ++ tailWord_784930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784930).length < 2 ^ (prefixWord ++ tailWord_784930).sum := by decide
  have hdescent : baseEnd_784930 < baseStart_784930 := by decide
  rcases family_descends (prefixWord ++ tailWord_784930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784944 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_784944 : Nat := 118140960795 + 784944 * 2 ^ 59
def prefixEnd_784944 : Nat := 4983230072969 + 3 ^ 40 * 784944 * 2
def baseEnd_784944 : Nat := 358269830100339677057879

theorem tailTrace_784944 : CollatzResearch.WordTrace tailWord_784944 prefixEnd_784944 358269830100339677057879 := by
  unfold tailWord_784944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314629834144710303712943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19086173112192947071617257 14314629834144710303712943)
  ·
    refine ⟨21471944751217065455569415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14314629834144710303712943 21471944751217065455569415)
    ·
      refine ⟨32207917126825598183354123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21471944751217065455569415 32207917126825598183354123)
      ·
        refine ⟨48311875690238397275031185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32207917126825598183354123 48311875690238397275031185)
        ·
          refine ⟨36233906767678797956273389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48311875690238397275031185 36233906767678797956273389)
          ·
            refine ⟨13587715037879549233602521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36233906767678797956273389 13587715037879549233602521)
            ·
              refine ⟨10190786278409661925201891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13587715037879549233602521 10190786278409661925201891)
              ·
                refine ⟨15286179417614492887802837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190786278409661925201891 15286179417614492887802837)
                ·
                  refine ⟨358269830100339677057879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15286179417614492887802837 358269830100339677057879)
                  ·
                    rfl

theorem cell20_784944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_784944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784944 prefixEnd_784944 := by exact prefixLift 784944
  have htrace : WordTrace (prefixWord ++ tailWord_784944) baseStart_784944 baseEnd_784944 := by
    simpa [prefixWord, tailWord_784944, baseEnd_784944] using wordTrace_append hprefix tailTrace_784944
  have hstable : (prefixWord ++ tailWord_784944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784944).length < 2 ^ (prefixWord ++ tailWord_784944).sum := by decide
  have hdescent : baseEnd_784944 < baseStart_784944 := by decide
  rcases family_descends (prefixWord ++ tailWord_784944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784947 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 2]
def baseStart_784947 : Nat := 118140960795 + 784947 * 2 ^ 59
def prefixEnd_784947 : Nat := 4983230072969 + 3 ^ 40 * 784947 * 2
def baseEnd_784947 : Nat := 358271199382084999957867

theorem tailTrace_784947 : CollatzResearch.WordTrace tailWord_784947 prefixEnd_784947 358271199382084999957867 := by
  unfold tailWord_784947
  simp only [CollatzResearch.WordTrace]
  refine ⟨28629369087278552119785095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19086246058185701413190063 28629369087278552119785095)
  ·
    refine ⟨42944053630917828179677643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28629369087278552119785095 42944053630917828179677643)
    ·
      refine ⟨64416080446376742269516465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42944053630917828179677643 64416080446376742269516465)
      ·
        refine ⟨48312060334782556702137349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64416080446376742269516465 48312060334782556702137349)
        ·
          refine ⟨9058511312771729381650753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48312060334782556702137349 9058511312771729381650753)
          ·
            refine ⟨6793883484578797036238065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058511312771729381650753 6793883484578797036238065)
            ·
              refine ⟨5095412613434097777178549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6793883484578797036238065 5095412613434097777178549)
              ·
                refine ⟨477694932509446666610489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5095412613434097777178549 477694932509446666610489)
                ·
                  refine ⟨358271199382084999957867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477694932509446666610489 358271199382084999957867)
                  ·
                    rfl

theorem cell20_784947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 2].length) (baseStart_784947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784947 prefixEnd_784947 := by exact prefixLift 784947
  have htrace : WordTrace (prefixWord ++ tailWord_784947) baseStart_784947 baseEnd_784947 := by
    simpa [prefixWord, tailWord_784947, baseEnd_784947] using wordTrace_append hprefix tailTrace_784947
  have hstable : (prefixWord ++ tailWord_784947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784947).length < 2 ^ (prefixWord ++ tailWord_784947).sum := by decide
  have hdescent : baseEnd_784947 < baseStart_784947 := by decide
  rcases family_descends (prefixWord ++ tailWord_784947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784975 : List Nat := [1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_784975 : Nat := 118140960795 + 784975 * 2 ^ 59
def prefixEnd_784975 : Nat := 4983230072969 + 3 ^ 40 * 784975 * 2
def baseEnd_784975 : Nat := 119427993115013782341473

theorem tailTrace_784975 : CollatzResearch.WordTrace tailWord_784975 prefixEnd_784975 119427993115013782341473 := by
  unfold tailWord_784975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28630390331177112901804379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19086926887451408601202919 28630390331177112901804379)
  ·
    refine ⟨42945585496765669352706569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28630390331177112901804379 42945585496765669352706569)
    ·
      refine ⟨32209189122574252014529927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42945585496765669352706569 32209189122574252014529927)
      ·
        refine ⟨48313783683861378021794891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32209189122574252014529927 48313783683861378021794891)
        ·
          refine ⟨72470675525792067032692337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48313783683861378021794891 72470675525792067032692337)
          ·
            refine ⟨54353006644344050274519253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72470675525792067032692337 54353006644344050274519253)
            ·
              refine ⟨1273898593226813678309045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54353006644344050274519253 1273898593226813678309045)
              ·
                refine ⟨119427993115013782341473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1273898593226813678309045 119427993115013782341473)
                ·
                  rfl

theorem cell20_784975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_784975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_784975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_784975 prefixEnd_784975 := by exact prefixLift 784975
  have htrace : WordTrace (prefixWord ++ tailWord_784975) baseStart_784975 baseEnd_784975 := by
    simpa [prefixWord, tailWord_784975, baseEnd_784975] using wordTrace_append hprefix tailTrace_784975
  have hstable : (prefixWord ++ tailWord_784975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784975).length < 2 ^ (prefixWord ++ tailWord_784975).sum := by decide
  have hdescent : baseEnd_784975 < baseStart_784975 := by decide
  rcases family_descends (prefixWord ++ tailWord_784975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785002 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_785002 : Nat := 118140960795 + 785002 * 2 ^ 59
def prefixEnd_785002 : Nat := 4983230072969 + 3 ^ 40 * 785002 * 2
def baseEnd_785002 : Nat := 358296302880749253124309

theorem tailTrace_785002 : CollatzResearch.WordTrace tailWord_785002 prefixEnd_785002 358296302880749253124309 := by
  unfold tailWord_785002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157843775519824128259315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19087583401386197675358173 7157843775519824128259315)
  ·
    refine ⟨10736765663279736192388973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7157843775519824128259315 10736765663279736192388973)
    ·
      refine ⟨4026287123729901072145865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10736765663279736192388973 4026287123729901072145865)
      ·
        refine ⟨3019715342797425804109399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4026287123729901072145865 3019715342797425804109399)
        ·
          refine ⟨4529573014196138706164099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019715342797425804109399 4529573014196138706164099)
          ·
            refine ⟨6794359521294208059246149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529573014196138706164099 6794359521294208059246149)
            ·
              refine ⟨1273942410242664011108653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6794359521294208059246149 1273942410242664011108653)
              ·
                refine ⟨477728403840999004165745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1273942410242664011108653 477728403840999004165745)
                ·
                  refine ⟨358296302880749253124309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477728403840999004165745 358296302880749253124309)
                  ·
                    rfl

theorem cell20_785002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_785002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785002 prefixEnd_785002 := by exact prefixLift 785002
  have htrace : WordTrace (prefixWord ++ tailWord_785002) baseStart_785002 baseEnd_785002 := by
    simpa [prefixWord, tailWord_785002, baseEnd_785002] using wordTrace_append hprefix tailTrace_785002
  have hstable : (prefixWord ++ tailWord_785002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785002).length < 2 ^ (prefixWord ++ tailWord_785002).sum := by decide
  have hdescent : baseEnd_785002 < baseStart_785002 := by decide
  rcases family_descends (prefixWord ++ tailWord_785002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785057 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 2]
def baseStart_785057 : Nat := 118140960795 + 785057 * 2 ^ 59
def prefixEnd_785057 : Nat := 4983230072969 + 3 ^ 40 * 785057 * 2
def baseEnd_785057 : Nat := 358321406379413506290751

theorem tailTrace_785057 : CollatzResearch.WordTrace tailWord_785057 prefixEnd_785057 358321406379413506290751 := by
  unfold tailWord_785057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28633381116880040906289425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19088920744586693937526283 28633381116880040906289425)
  ·
    refine ⟨21475035837660030679717069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28633381116880040906289425 21475035837660030679717069)
    ·
      refine ⟨8053138439122511504893901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21475035837660030679717069 8053138439122511504893901)
      ·
        refine ⟨3019926914670941814335213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8053138439122511504893901 3019926914670941814335213)
        ·
          refine ⟨1132472593001603180375705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3019926914670941814335213 1132472593001603180375705)
          ·
            refine ⟨849354444751202385281779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132472593001603180375705 849354444751202385281779)
            ·
              refine ⟨1274031667126803577922669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849354444751202385281779 1274031667126803577922669)
              ·
                refine ⟨477761875172551341721001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1274031667126803577922669 477761875172551341721001)
                ·
                  refine ⟨358321406379413506290751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477761875172551341721001 358321406379413506290751)
                  ·
                    rfl

theorem cell20_785057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_785057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785057 prefixEnd_785057 := by exact prefixLift 785057
  have htrace : WordTrace (prefixWord ++ tailWord_785057) baseStart_785057 baseEnd_785057 := by
    simpa [prefixWord, tailWord_785057, baseEnd_785057] using wordTrace_append hprefix tailTrace_785057
  have hstable : (prefixWord ++ tailWord_785057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785057).length < 2 ^ (prefixWord ++ tailWord_785057).sum := by decide
  have hdescent : baseEnd_785057 < baseStart_785057 := by decide
  rcases family_descends (prefixWord ++ tailWord_785057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785065 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_785065 : Nat := 118140960795 + 785065 * 2 ^ 59
def prefixEnd_785065 : Nat := 4983230072969 + 3 ^ 40 * 785065 * 2
def baseEnd_785065 : Nat := 358325057797401034024051

theorem tailTrace_785065 : CollatzResearch.WordTrace tailWord_785065 prefixEnd_785065 358325057797401034024051 := by
  unfold tailWord_785065
  simp only [CollatzResearch.WordTrace]
  refine ⟨28633672900851058272580649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19089115267234038848387099 28633672900851058272580649)
  ·
    refine ⟨21475254675638293704435487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28633672900851058272580649 21475254675638293704435487)
    ·
      refine ⟨32212882013457440556653231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21475254675638293704435487 32212882013457440556653231)
      ·
        refine ⟨48319323020186160834979847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32212882013457440556653231 48319323020186160834979847)
        ·
          refine ⟨72478984530279241252469771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48319323020186160834979847 72478984530279241252469771)
          ·
            refine ⟨108718476795418861878704657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72478984530279241252469771 108718476795418861878704657)
            ·
              refine ⟨81538857596564146409028493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108718476795418861878704657 81538857596564146409028493)
              ·
                refine ⟨30577071598711554903385685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81538857596564146409028493 30577071598711554903385685)
                ·
                  refine ⟨358325057797401034024051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30577071598711554903385685 358325057797401034024051)
                  ·
                    rfl

theorem cell20_785065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_785065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785065 prefixEnd_785065 := by exact prefixLift 785065
  have htrace : WordTrace (prefixWord ++ tailWord_785065) baseStart_785065 baseEnd_785065 := by
    simpa [prefixWord, tailWord_785065, baseEnd_785065] using wordTrace_append hprefix tailTrace_785065
  have hstable : (prefixWord ++ tailWord_785065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785065).length < 2 ^ (prefixWord ++ tailWord_785065).sum := by decide
  have hdescent : baseEnd_785065 < baseStart_785065 := by decide
  rcases family_descends (prefixWord ++ tailWord_785065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785092 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_785092 : Nat := 118140960795 + 785092 * 2 ^ 59
def prefixEnd_785092 : Nat := 4983230072969 + 3 ^ 40 * 785092 * 2
def baseEnd_785092 : Nat := 358337381333108940123941

theorem tailTrace_785092 : CollatzResearch.WordTrace tailWord_785092 prefixEnd_785092 358337381333108940123941 := by
  unfold tailWord_785092
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317328835876620941906765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19089771781168827922542353 14317328835876620941906765)
  ·
    refine ⟨5368998313453732853215037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14317328835876620941906765 5368998313453732853215037)
    ·
      refine ⟨2013374367545149819955639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5368998313453732853215037 2013374367545149819955639)
      ·
        refine ⟨3020061551317724729933459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013374367545149819955639 3020061551317724729933459)
        ·
          refine ⟨4530092326976587094900189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020061551317724729933459 4530092326976587094900189)
          ·
            refine ⟨1698784622616220160587571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4530092326976587094900189 1698784622616220160587571)
            ·
              refine ⟨2548176933924330240881357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698784622616220160587571 2548176933924330240881357)
              ·
                refine ⟨955566350221623840330509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548176933924330240881357 955566350221623840330509)
                ·
                  refine ⟨358337381333108940123941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955566350221623840330509 358337381333108940123941)
                  ·
                    rfl

theorem cell20_785092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_785092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785092 prefixEnd_785092 := by exact prefixLift 785092
  have htrace : WordTrace (prefixWord ++ tailWord_785092) baseStart_785092 baseEnd_785092 := by
    simpa [prefixWord, tailWord_785092, baseEnd_785092] using wordTrace_append hprefix tailTrace_785092
  have hstable : (prefixWord ++ tailWord_785092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785092).length < 2 ^ (prefixWord ++ tailWord_785092).sum := by decide
  have hdescent : baseEnd_785092 < baseStart_785092 := by decide
  rcases family_descends (prefixWord ++ tailWord_785092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785137 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 2]
def baseStart_785137 : Nat := 118140960795 + 785137 * 2 ^ 59
def prefixEnd_785137 : Nat := 4983230072969 + 3 ^ 40 * 785137 * 2
def baseEnd_785137 : Nat := 358357920559288783623757

theorem tailTrace_785137 : CollatzResearch.WordTrace tailWord_785137 prefixEnd_785137 358357920559288783623757 := by
  unfold tailWord_785137
  simp only [CollatzResearch.WordTrace]
  refine ⟨28636298956590214569201665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19090865971060143046134443 28636298956590214569201665)
  ·
    refine ⟨21477224217442660926901249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28636298956590214569201665 21477224217442660926901249)
    ·
      refine ⟨16107918163081995695175937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21477224217442660926901249 16107918163081995695175937)
      ·
        refine ⟨12080938622311496771381953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16107918163081995695175937 12080938622311496771381953)
        ·
          refine ⟨9060703966733622578536465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12080938622311496771381953 9060703966733622578536465)
          ·
            refine ⟨6795527975050216933902349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9060703966733622578536465 6795527975050216933902349)
            ·
              refine ⟨2548322990643831350213381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6795527975050216933902349 2548322990643831350213381)
              ·
                refine ⟨477810560745718378165009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2548322990643831350213381 477810560745718378165009)
                ·
                  refine ⟨358357920559288783623757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477810560745718378165009 358357920559288783623757)
                  ·
                    rfl

theorem cell20_785137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_785137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785137 prefixEnd_785137 := by exact prefixLift 785137
  have htrace : WordTrace (prefixWord ++ tailWord_785137) baseStart_785137 baseEnd_785137 := by
    simpa [prefixWord, tailWord_785137, baseEnd_785137] using wordTrace_append hprefix tailTrace_785137
  have hstable : (prefixWord ++ tailWord_785137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785137).length < 2 ^ (prefixWord ++ tailWord_785137).sum := by decide
  have hdescent : baseEnd_785137 < baseStart_785137 := by decide
  rcases family_descends (prefixWord ++ tailWord_785137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785196 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_785196 : Nat := 118140960795 + 785196 * 2 ^ 59
def prefixEnd_785196 : Nat := 4983230072969 + 3 ^ 40 * 785196 * 2
def baseEnd_785196 : Nat := 358384849766946800656849

theorem tailTrace_785196 : CollatzResearch.WordTrace tailWord_785196 prefixEnd_785196 358384849766946800656849 := by
  unfold tailWord_785196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319225431688233822799721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19092300575584311763732961 14319225431688233822799721)
  ·
    refine ⟨10739419073766175367099791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14319225431688233822799721 10739419073766175367099791)
    ·
      refine ⟨16109128610649263050649687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10739419073766175367099791 16109128610649263050649687)
      ·
        refine ⟨24163692915973894575974531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16109128610649263050649687 24163692915973894575974531)
        ·
          refine ⟨36245539373960841863961797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24163692915973894575974531 36245539373960841863961797)
          ·
            refine ⟨6796038632617657849492837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36245539373960841863961797 6796038632617657849492837)
            ·
              refine ⟨1274257243615810846779907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6796038632617657849492837 1274257243615810846779907)
              ·
                refine ⟨1911385865423716270169861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274257243615810846779907 1911385865423716270169861)
                ·
                  refine ⟨358384849766946800656849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911385865423716270169861 358384849766946800656849)
                  ·
                    rfl

theorem cell20_785196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_785196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785196 prefixEnd_785196 := by exact prefixLift 785196
  have htrace : WordTrace (prefixWord ++ tailWord_785196) baseStart_785196 baseEnd_785196 := by
    simpa [prefixWord, tailWord_785196, baseEnd_785196] using wordTrace_append hprefix tailTrace_785196
  have hstable : (prefixWord ++ tailWord_785196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785196).length < 2 ^ (prefixWord ++ tailWord_785196).sum := by decide
  have hdescent : baseEnd_785196 < baseStart_785196 := by decide
  rcases family_descends (prefixWord ++ tailWord_785196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785241 : List Nat := [1, 2, 1, 2, 2, 6, 6]
def baseStart_785241 : Nat := 118140960795 + 785241 * 2 ^ 59
def prefixEnd_785241 : Nat := 4983230072969 + 3 ^ 40 * 785241 * 2
def baseEnd_785241 : Nat := 39822820999236293795185

theorem tailTrace_785241 : CollatzResearch.WordTrace tailWord_785241 prefixEnd_785241 39822820999236293795185 := by
  unfold tailWord_785241
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640092148213440330987577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19093394765475626887325051 28640092148213440330987577)
  ·
    refine ⟨21480069111160080248240683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28640092148213440330987577 21480069111160080248240683)
    ·
      refine ⟨32220103666740120372361025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21480069111160080248240683 32220103666740120372361025)
      ·
        refine ⟨24165077750055090279270769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32220103666740120372361025 24165077750055090279270769)
        ·
          refine ⟨18123808312541317709453077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24165077750055090279270769 18123808312541317709453077)
          ·
            refine ⟨849553514650374267630613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18123808312541317709453077 849553514650374267630613)
            ·
              refine ⟨39822820999236293795185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 849553514650374267630613 39822820999236293795185)
              ·
                rfl

theorem cell20_785241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_785241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785241 prefixEnd_785241 := by exact prefixLift 785241
  have htrace : WordTrace (prefixWord ++ tailWord_785241) baseStart_785241 baseEnd_785241 := by
    simpa [prefixWord, tailWord_785241, baseEnd_785241] using wordTrace_append hprefix tailTrace_785241
  have hstable : (prefixWord ++ tailWord_785241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785241).length < 2 ^ (prefixWord ++ tailWord_785241).sum := by decide
  have hdescent : baseEnd_785241 < baseStart_785241 := by decide
  rcases family_descends (prefixWord ++ tailWord_785241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785248 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_785248 : Nat := 118140960795 + 785248 * 2 ^ 59
def prefixEnd_785248 : Nat := 4983230072969 + 3 ^ 40 * 785248 * 2
def baseEnd_785248 : Nat := 358408583983865730923303

theorem tailTrace_785248 : CollatzResearch.WordTrace tailWord_785248 prefixEnd_785248 358408583983865730923303 := by
  unfold tailWord_785248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14320173729594040263246199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19093564972792053684328265 14320173729594040263246199)
  ·
    refine ⟨21480260594391060394869299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14320173729594040263246199 21480260594391060394869299)
    ·
      refine ⟨32220390891586590592303949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21480260594391060394869299 32220390891586590592303949)
      ·
        refine ⟨12082646584344971472113981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32220390891586590592303949 12082646584344971472113981)
        ·
          refine ⟨4530992469129364302042743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12082646584344971472113981 4530992469129364302042743)
          ·
            refine ⟨6796488703694046453064115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530992469129364302042743 6796488703694046453064115)
            ·
              refine ⟨10194733055541069679596173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796488703694046453064115 10194733055541069679596173)
              ·
                refine ⟨3823024895827901129848565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10194733055541069679596173 3823024895827901129848565)
                ·
                  refine ⟨358408583983865730923303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3823024895827901129848565 358408583983865730923303)
                  ·
                    rfl

theorem cell20_785248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_785248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785248 prefixEnd_785248 := by exact prefixLift 785248
  have htrace : WordTrace (prefixWord ++ tailWord_785248) baseStart_785248 baseEnd_785248 := by
    simpa [prefixWord, tailWord_785248, baseEnd_785248] using wordTrace_append hprefix tailTrace_785248
  have hstable : (prefixWord ++ tailWord_785248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785248).length < 2 ^ (prefixWord ++ tailWord_785248).sum := by decide
  have hdescent : baseEnd_785248 < baseStart_785248 := by decide
  rcases family_descends (prefixWord ++ tailWord_785248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785251 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 4]
def baseStart_785251 : Nat := 118140960795 + 785251 * 2 ^ 59
def prefixEnd_785251 : Nat := 4983230072969 + 3 ^ 40 * 785251 * 2
def baseEnd_785251 : Nat := 358409953265611053823291

theorem tailTrace_785251 : CollatzResearch.WordTrace tailWord_785251 prefixEnd_785251 358409953265611053823291 := by
  unfold tailWord_785251
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640456878177212038851607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19093637918784808025901071 28640456878177212038851607)
  ·
    refine ⟨42960685317265818058277411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28640456878177212038851607 42960685317265818058277411)
    ·
      refine ⟨64441027975898727087416117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42960685317265818058277411 64441027975898727087416117)
      ·
        refine ⟨6041346372740505664445261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64441027975898727087416117 6041346372740505664445261)
        ·
          refine ⟨2265504889777689624166973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6041346372740505664445261 2265504889777689624166973)
          ·
            refine ⟨849564333666633609062615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2265504889777689624166973 849564333666633609062615)
            ·
              refine ⟨1274346500499950413593923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849564333666633609062615 1274346500499950413593923)
              ·
                refine ⟨1911519750749925620390885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274346500499950413593923 1911519750749925620390885)
                ·
                  refine ⟨358409953265611053823291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911519750749925620390885 358409953265611053823291)
                  ·
                    rfl

theorem cell20_785251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_785251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785251 prefixEnd_785251 := by exact prefixLift 785251
  have htrace : WordTrace (prefixWord ++ tailWord_785251) baseStart_785251 baseEnd_785251 := by
    simpa [prefixWord, tailWord_785251, baseEnd_785251] using wordTrace_append hprefix tailTrace_785251
  have hstable : (prefixWord ++ tailWord_785251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785251).length < 2 ^ (prefixWord ++ tailWord_785251).sum := by decide
  have hdescent : baseEnd_785251 < baseStart_785251 := by decide
  rcases family_descends (prefixWord ++ tailWord_785251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785265 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_785265 : Nat := 118140960795 + 785265 * 2 ^ 59
def prefixEnd_785265 : Nat := 4983230072969 + 3 ^ 40 * 785265 * 2
def baseEnd_785265 : Nat := 358416343247089227356567

theorem tailTrace_785265 : CollatzResearch.WordTrace tailWord_785265 prefixEnd_785265 358416343247089227356567 := by
  unfold tailWord_785265
  simp only [CollatzResearch.WordTrace]
  refine ⟨28640967500126492429861249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19093978333417661619907499 28640967500126492429861249)
  ·
    refine ⟨21480725625094869322395937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28640967500126492429861249 21480725625094869322395937)
    ·
      refine ⟨16110544218821151991796953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21480725625094869322395937 16110544218821151991796953)
      ·
        refine ⟨12082908164115863993847715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16110544218821151991796953 12082908164115863993847715)
        ·
          refine ⟨18124362246173795990771573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12082908164115863993847715 18124362246173795990771573)
          ·
            refine ⟨1699158960578793374134835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18124362246173795990771573 1699158960578793374134835)
            ·
              refine ⟨2548738440868190061202253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699158960578793374134835 2548738440868190061202253)
              ·
                refine ⟨955776915325571272950845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548738440868190061202253 955776915325571272950845)
                ·
                  refine ⟨358416343247089227356567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955776915325571272950845 358416343247089227356567)
                  ·
                    rfl

theorem cell20_785265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_785265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785265 prefixEnd_785265 := by exact prefixLift 785265
  have htrace : WordTrace (prefixWord ++ tailWord_785265) baseStart_785265 baseEnd_785265 := by
    simpa [prefixWord, tailWord_785265, baseEnd_785265] using wordTrace_append hprefix tailTrace_785265
  have hstable : (prefixWord ++ tailWord_785265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785265).length < 2 ^ (prefixWord ++ tailWord_785265).sum := by decide
  have hdescent : baseEnd_785265 < baseStart_785265 := by decide
  rcases family_descends (prefixWord ++ tailWord_785265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785302 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_785302 : Nat := 118140960795 + 785302 * 2 ^ 59
def prefixEnd_785302 : Nat := 4983230072969 + 3 ^ 40 * 785302 * 2
def baseEnd_785302 : Nat := 358433231055281543123083

theorem tailTrace_785302 : CollatzResearch.WordTrace tailWord_785302 prefixEnd_785302 358433231055281543123083 := by
  unfold tailWord_785302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790144812562027984309885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19094878000661631832638773 1790144812562027984309885)
  ·
    refine ⟨671304304710760494116207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1790144812562027984309885 671304304710760494116207)
    ·
      refine ⟨1006956457066140741174311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671304304710760494116207 1006956457066140741174311)
      ·
        refine ⟨1510434685599211111761467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006956457066140741174311 1510434685599211111761467)
        ·
          refine ⟨2265652028398816667642201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510434685599211111761467 2265652028398816667642201)
          ·
            refine ⟨1699239021299112500731651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2265652028398816667642201 1699239021299112500731651)
            ·
              refine ⟨2548858531948668751097477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699239021299112500731651 2548858531948668751097477)
              ·
                refine ⟨477910974740375390830777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2548858531948668751097477 477910974740375390830777)
                ·
                  refine ⟨358433231055281543123083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477910974740375390830777 358433231055281543123083)
                  ·
                    rfl

theorem cell20_785302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_785302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785302 prefixEnd_785302 := by exact prefixLift 785302
  have htrace : WordTrace (prefixWord ++ tailWord_785302) baseStart_785302 baseEnd_785302 := by
    simpa [prefixWord, tailWord_785302, baseEnd_785302] using wordTrace_append hprefix tailTrace_785302
  have hstable : (prefixWord ++ tailWord_785302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785302).length < 2 ^ (prefixWord ++ tailWord_785302).sum := by decide
  have hdescent : baseEnd_785302 < baseStart_785302 := by decide
  rcases family_descends (prefixWord ++ tailWord_785302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785303 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_785303 : Nat := 118140960795 + 785303 * 2 ^ 59
def prefixEnd_785303 : Nat := 4983230072969 + 3 ^ 40 * 785303 * 2
def baseEnd_785303 : Nat := 358433687482529984089745

theorem tailTrace_785303 : CollatzResearch.WordTrace tailWord_785303 prefixEnd_785303 358433687482529984089745 := by
  unfold tailWord_785303
  simp only [CollatzResearch.WordTrace]
  refine ⟨28642353473988824919744563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19094902315992549946496375 28642353473988824919744563)
  ·
    refine ⟨42963530210983237379616845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28642353473988824919744563 42963530210983237379616845)
    ·
      refine ⟨16111323829118714017356317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42963530210983237379616845 16111323829118714017356317)
      ·
        refine ⟨6041746435919517756508619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16111323829118714017356317 6041746435919517756508619)
        ·
          refine ⟨9062619653879276634762929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041746435919517756508619 9062619653879276634762929)
          ·
            refine ⟨6796964740409457476072197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9062619653879276634762929 6796964740409457476072197)
            ·
              refine ⟨1274430888826773276763537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6796964740409457476072197 1274430888826773276763537)
              ·
                refine ⟨955823166620079957572653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274430888826773276763537 955823166620079957572653)
                ·
                  refine ⟨358433687482529984089745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955823166620079957572653 358433687482529984089745)
                  ·
                    rfl

theorem cell20_785303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_785303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785303 prefixEnd_785303 := by exact prefixLift 785303
  have htrace : WordTrace (prefixWord ++ tailWord_785303) baseStart_785303 baseEnd_785303 := by
    simpa [prefixWord, tailWord_785303, baseEnd_785303] using wordTrace_append hprefix tailTrace_785303
  have hstable : (prefixWord ++ tailWord_785303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785303).length < 2 ^ (prefixWord ++ tailWord_785303).sum := by decide
  have hdescent : baseEnd_785303 < baseStart_785303 := by decide
  rcases family_descends (prefixWord ++ tailWord_785303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785306 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_785306 : Nat := 118140960795 + 785306 * 2 ^ 59
def prefixEnd_785306 : Nat := 4983230072969 + 3 ^ 40 * 785306 * 2
def baseEnd_785306 : Nat := 358435056764275306989733

theorem tailTrace_785306 : CollatzResearch.WordTrace tailWord_785306 prefixEnd_785306 358435056764275306989733 := by
  unfold tailWord_785306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160615723244489108025943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19094975261985304288069181 7160615723244489108025943)
  ·
    refine ⟨10740923584866733662038915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160615723244489108025943 10740923584866733662038915)
    ·
      refine ⟨16111385377300100493058373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740923584866733662038915 16111385377300100493058373)
      ·
        refine ⟨3020884758243768842448445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16111385377300100493058373 3020884758243768842448445)
        ·
          refine ⟨1132831784341413315918167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3020884758243768842448445 1132831784341413315918167)
          ·
            refine ⟨1699247676512119973877251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132831784341413315918167 1699247676512119973877251)
            ·
              refine ⟨2548871514768179960815877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699247676512119973877251 2548871514768179960815877)
              ·
                refine ⟨477913409019033742652977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2548871514768179960815877 477913409019033742652977)
                ·
                  refine ⟨358435056764275306989733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477913409019033742652977 358435056764275306989733)
                  ·
                    rfl

theorem cell20_785306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_785306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785306 prefixEnd_785306 := by exact prefixLift 785306
  have htrace : WordTrace (prefixWord ++ tailWord_785306) baseStart_785306 baseEnd_785306 := by
    simpa [prefixWord, tailWord_785306, baseEnd_785306] using wordTrace_append hprefix tailTrace_785306
  have hstable : (prefixWord ++ tailWord_785306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785306).length < 2 ^ (prefixWord ++ tailWord_785306).sum := by decide
  have hdescent : baseEnd_785306 < baseStart_785306 := by decide
  rcases family_descends (prefixWord ++ tailWord_785306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785350 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_785350 : Nat := 118140960795 + 785350 * 2 ^ 59
def prefixEnd_785350 : Nat := 4983230072969 + 3 ^ 40 * 785350 * 2
def baseEnd_785350 : Nat := 358455139563206709522887

theorem tailTrace_785350 : CollatzResearch.WordTrace tailWord_785350 prefixEnd_785350 358455139563206709522887 := by
  unfold tailWord_785350
  simp only [CollatzResearch.WordTrace]
  refine ⟨895127115775579748334547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19096045136545701297803669 895127115775579748334547)
  ·
    refine ⟨1342690673663369622501821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 895127115775579748334547 1342690673663369622501821)
    ·
      refine ⟨503509002623763608438183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1342690673663369622501821 503509002623763608438183)
      ·
        refine ⟨755263503935645412657275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503509002623763608438183 755263503935645412657275)
        ·
          refine ⟨1132895255903468118985913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755263503935645412657275 1132895255903468118985913)
          ·
            refine ⟨849671441927601089239435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132895255903468118985913 849671441927601089239435)
            ·
              refine ⟨1274507162891401633859153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849671441927601089239435 1274507162891401633859153)
              ·
                refine ⟨955880372168551225394365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274507162891401633859153 955880372168551225394365)
                ·
                  refine ⟨358455139563206709522887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955880372168551225394365 358455139563206709522887)
                  ·
                    rfl

theorem cell20_785350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_785350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785350 prefixEnd_785350 := by exact prefixLift 785350
  have htrace : WordTrace (prefixWord ++ tailWord_785350) baseStart_785350 baseEnd_785350 := by
    simpa [prefixWord, tailWord_785350, baseEnd_785350] using wordTrace_append hprefix tailTrace_785350
  have hstable : (prefixWord ++ tailWord_785350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785350).length < 2 ^ (prefixWord ++ tailWord_785350).sum := by decide
  have hdescent : baseEnd_785350 < baseStart_785350 := by decide
  rcases family_descends (prefixWord ++ tailWord_785350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785358 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_785358 : Nat := 118140960795 + 785358 * 2 ^ 59
def prefixEnd_785358 : Nat := 4983230072969 + 3 ^ 40 * 785358 * 2
def baseEnd_785358 : Nat := 358458790981194237256187

theorem tailTrace_785358 : CollatzResearch.WordTrace tailWord_785358 prefixEnd_785358 358458790981194237256187 := by
  unfold tailWord_785358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580544936098696164124591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19096239659193046208664485 3580544936098696164124591)
  ·
    refine ⟨5370817404148044246186887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3580544936098696164124591 5370817404148044246186887)
    ·
      refine ⟨8056226106222066369280331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5370817404148044246186887 8056226106222066369280331)
      ·
        refine ⟨12084339159333099553920497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8056226106222066369280331 12084339159333099553920497)
        ·
          refine ⟨9063254369499824665440373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12084339159333099553920497 9063254369499824665440373)
          ·
            refine ⟨849680097140608562385035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9063254369499824665440373 849680097140608562385035)
            ·
              refine ⟨1274520145710912843577553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849680097140608562385035 1274520145710912843577553)
              ·
                refine ⟨955890109283184632683165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274520145710912843577553 955890109283184632683165)
                ·
                  refine ⟨358458790981194237256187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955890109283184632683165 358458790981194237256187)
                  ·
                    rfl

theorem cell20_785358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_785358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785358 prefixEnd_785358 := by exact prefixLift 785358
  have htrace : WordTrace (prefixWord ++ tailWord_785358) baseStart_785358 baseEnd_785358 := by
    simpa [prefixWord, tailWord_785358, baseEnd_785358] using wordTrace_append hprefix tailTrace_785358
  have hstable : (prefixWord ++ tailWord_785358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785358).length < 2 ^ (prefixWord ++ tailWord_785358).sum := by decide
  have hdescent : baseEnd_785358 < baseStart_785358 := by decide
  rcases family_descends (prefixWord ++ tailWord_785358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785365 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_785365 : Nat := 118140960795 + 785365 * 2 ^ 59
def prefixEnd_785365 : Nat := 4983230072969 + 3 ^ 40 * 785365 * 2
def baseEnd_785365 : Nat := 358461985971933324022825

theorem tailTrace_785365 : CollatzResearch.WordTrace tailWord_785365 prefixEnd_785365 358461985971933324022825 := by
  unfold tailWord_785365
  simp only [CollatzResearch.WordTrace]
  refine ⟨28644614799764209508501549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19096409866509473005667699 28644614799764209508501549)
  ·
    refine ⟨10741730549911578565688081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28644614799764209508501549 10741730549911578565688081)
    ·
      refine ⟨8056297912433683924266061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10741730549911578565688081 8056297912433683924266061)
      ·
        refine ⟨3021111717162631471599773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8056297912433683924266061 3021111717162631471599773)
        ·
          refine ⟨1132916893935986801849915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3021111717162631471599773 1132916893935986801849915)
          ·
            refine ⟨1699375340903980202774873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132916893935986801849915 1699375340903980202774873)
            ·
              refine ⟨1274531505677985152081155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1699375340903980202774873 1274531505677985152081155)
              ·
                refine ⟨1911797258516977728121733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274531505677985152081155 1911797258516977728121733)
                ·
                  refine ⟨358461985971933324022825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911797258516977728121733 358461985971933324022825)
                  ·
                    rfl

theorem cell20_785365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_785365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785365 prefixEnd_785365 := by exact prefixLift 785365
  have htrace : WordTrace (prefixWord ++ tailWord_785365) baseStart_785365 baseEnd_785365 := by
    simpa [prefixWord, tailWord_785365, baseEnd_785365] using wordTrace_append hprefix tailTrace_785365
  have hstable : (prefixWord ++ tailWord_785365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785365).length < 2 ^ (prefixWord ++ tailWord_785365).sum := by decide
  have hdescent : baseEnd_785365 < baseStart_785365 := by decide
  rcases family_descends (prefixWord ++ tailWord_785365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785386 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_785386 : Nat := 118140960795 + 785386 * 2 ^ 59
def prefixEnd_785386 : Nat := 4983230072969 + 3 ^ 40 * 785386 * 2
def baseEnd_785386 : Nat := 358471570944150584322739

theorem tailTrace_785386 : CollatzResearch.WordTrace tailWord_785386 prefixEnd_785386 358471570944150584322739 := by
  unfold tailWord_785386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161345183172032523754003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19096920488458753396677341 7161345183172032523754003)
  ·
    refine ⟨10742017774758048785631005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7161345183172032523754003 10742017774758048785631005)
    ·
      refine ⟨4028256665534268294611627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10742017774758048785631005 4028256665534268294611627)
      ·
        refine ⟨6042384998301402441917441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4028256665534268294611627 6042384998301402441917441)
        ·
          refine ⟨4531788748726051831438081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6042384998301402441917441 4531788748726051831438081)
          ·
            refine ⟨3398841561544538873578561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531788748726051831438081 3398841561544538873578561)
            ·
              refine ⟨2549131171158404155183921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398841561544538873578561 2549131171158404155183921)
              ·
                refine ⟨1911848378368803116387941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549131171158404155183921 1911848378368803116387941)
                ·
                  refine ⟨358471570944150584322739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911848378368803116387941 358471570944150584322739)
                  ·
                    rfl

theorem cell20_785386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_785386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785386 prefixEnd_785386 := by exact prefixLift 785386
  have htrace : WordTrace (prefixWord ++ tailWord_785386) baseStart_785386 baseEnd_785386 := by
    simpa [prefixWord, tailWord_785386, baseEnd_785386] using wordTrace_append hprefix tailTrace_785386
  have hstable : (prefixWord ++ tailWord_785386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785386).length < 2 ^ (prefixWord ++ tailWord_785386).sum := by decide
  have hdescent : baseEnd_785386 < baseStart_785386 := by decide
  rcases family_descends (prefixWord ++ tailWord_785386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785393 : List Nat := [1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_785393 : Nat := 118140960795 + 785393 * 2 ^ 59
def prefixEnd_785393 : Nat := 4983230072969 + 3 ^ 40 * 785393 * 2
def baseEnd_785393 : Nat := 119491588644963223696459

theorem tailTrace_785393 : CollatzResearch.WordTrace tailWord_785393 prefixEnd_785393 119491588644963223696459 := by
  unfold tailWord_785393
  simp only [CollatzResearch.WordTrace]
  refine ⟨28645636043662770290520833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19097090695775180193680555 28645636043662770290520833)
  ·
    refine ⟨21484227032747077717890625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28645636043662770290520833 21484227032747077717890625)
    ·
      refine ⟨16113170274560308288417969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21484227032747077717890625 16113170274560308288417969)
      ·
        refine ⟨12084877705920231216313477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16113170274560308288417969 12084877705920231216313477)
        ·
          refine ⟨2265914569860043353058777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12084877705920231216313477 2265914569860043353058777)
          ·
            refine ⟨1699435927395032514794083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2265914569860043353058777 1699435927395032514794083)
            ·
              refine ⟨2549153891092548772191125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699435927395032514794083 2549153891092548772191125)
              ·
                refine ⟨119491588644963223696459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2549153891092548772191125 119491588644963223696459)
                ·
                  rfl

theorem cell20_785393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_785393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785393 prefixEnd_785393 := by exact prefixLift 785393
  have htrace : WordTrace (prefixWord ++ tailWord_785393) baseStart_785393 baseEnd_785393 := by
    simpa [prefixWord, tailWord_785393, baseEnd_785393] using wordTrace_append hprefix tailTrace_785393
  have hstable : (prefixWord ++ tailWord_785393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785393).length < 2 ^ (prefixWord ++ tailWord_785393).sum := by decide
  have hdescent : baseEnd_785393 < baseStart_785393 := by decide
  rcases family_descends (prefixWord ++ tailWord_785393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785420 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 2]
def baseStart_785420 : Nat := 118140960795 + 785420 * 2 ^ 59
def prefixEnd_785420 : Nat := 4983230072969 + 3 ^ 40 * 785420 * 2
def baseEnd_785420 : Nat := 358487089470597577189267

theorem tailTrace_785420 : CollatzResearch.WordTrace tailWord_785420 prefixEnd_785420 358487089470597577189267 := by
  unfold tailWord_785420
  simp only [CollatzResearch.WordTrace]
  refine ⟨14323310407282476950876857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19097747209709969267835809 14323310407282476950876857)
  ·
    refine ⟨10742482805461857713157643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14323310407282476950876857 10742482805461857713157643)
    ·
      refine ⟨16113724208192786569736465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742482805461857713157643 16113724208192786569736465)
      ·
        refine ⟨12085293156144589927302349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16113724208192786569736465 12085293156144589927302349)
        ·
          refine ⟨4531984933554221222738381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12085293156144589927302349 4531984933554221222738381)
          ·
            refine ⟨1699494350082832958526893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4531984933554221222738381 1699494350082832958526893)
            ·
              refine ⟨637310381281062359447585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1699494350082832958526893 637310381281062359447585)
              ·
                refine ⟨477982785960796769585689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637310381281062359447585 477982785960796769585689)
                ·
                  refine ⟨358487089470597577189267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477982785960796769585689 358487089470597577189267)
                  ·
                    rfl

theorem cell20_785420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_785420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785420 prefixEnd_785420 := by exact prefixLift 785420
  have htrace : WordTrace (prefixWord ++ tailWord_785420) baseStart_785420 baseEnd_785420 := by
    simpa [prefixWord, tailWord_785420, baseEnd_785420] using wordTrace_append hprefix tailTrace_785420
  have hstable : (prefixWord ++ tailWord_785420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785420).length < 2 ^ (prefixWord ++ tailWord_785420).sum := by decide
  have hdescent : baseEnd_785420 < baseStart_785420 := by decide
  rcases family_descends (prefixWord ++ tailWord_785420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785426 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_785426 : Nat := 118140960795 + 785426 * 2 ^ 59
def prefixEnd_785426 : Nat := 4983230072969 + 3 ^ 40 * 785426 * 2
def baseEnd_785426 : Nat := 358489828034088222989243

theorem tailTrace_785426 : CollatzResearch.WordTrace tailWord_785426 prefixEnd_785426 358489828034088222989243 := by
  unfold tailWord_785426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161709913135804231618033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19097893101695477950981421 7161709913135804231618033)
  ·
    refine ⟨5371282434851853173713525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7161709913135804231618033 5371282434851853173713525)
    ·
      refine ⟨503557728267361235035643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5371282434851853173713525 503557728267361235035643)
      ·
        refine ⟨755336592401041852553465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503557728267361235035643 755336592401041852553465)
        ·
          refine ⟨566502444300781389415099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755336592401041852553465 566502444300781389415099)
          ·
            refine ⟨849753666451172084122649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566502444300781389415099 849753666451172084122649)
            ·
              refine ⟨637315249838379063091987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849753666451172084122649 637315249838379063091987)
              ·
                refine ⟨955972874757568594637981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637315249838379063091987 955972874757568594637981)
                ·
                  refine ⟨358489828034088222989243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955972874757568594637981 358489828034088222989243)
                  ·
                    rfl

theorem cell20_785426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_785426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785426 prefixEnd_785426 := by exact prefixLift 785426
  have htrace : WordTrace (prefixWord ++ tailWord_785426) baseStart_785426 baseEnd_785426 := by
    simpa [prefixWord, tailWord_785426, baseEnd_785426] using wordTrace_append hprefix tailTrace_785426
  have hstable : (prefixWord ++ tailWord_785426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785426).length < 2 ^ (prefixWord ++ tailWord_785426).sum := by decide
  have hdescent : baseEnd_785426 < baseStart_785426 := by decide
  rcases family_descends (prefixWord ++ tailWord_785426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785431 : List Nat := [1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_785431 : Nat := 118140960795 + 785431 * 2 ^ 59
def prefixEnd_785431 : Nat := 4983230072969 + 3 ^ 40 * 785431 * 2
def baseEnd_785431 : Nat := 119497370056776809274185

theorem tailTrace_785431 : CollatzResearch.WordTrace tailWord_785431 prefixEnd_785431 119497370056776809274185 := by
  unfold tailWord_785431
  simp only [CollatzResearch.WordTrace]
  refine ⟨28647022017525102780404147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19098014678350068520269431 28647022017525102780404147)
  ·
    refine ⟨42970533026287654170606221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28647022017525102780404147 42970533026287654170606221)
    ·
      refine ⟨16113949884857870313977333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42970533026287654170606221 16113949884857870313977333)
      ·
        refine ⟨1510682801705425341935375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16113949884857870313977333 1510682801705425341935375)
        ·
          refine ⟨2266024202558138012903063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510682801705425341935375 2266024202558138012903063)
          ·
            refine ⟨3399036303837207019354595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266024202558138012903063 3399036303837207019354595)
            ·
              refine ⟨5098554455755810529031893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399036303837207019354595 5098554455755810529031893)
              ·
                refine ⟨119497370056776809274185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5098554455755810529031893 119497370056776809274185)
                ·
                  rfl

theorem cell20_785431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_785431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785431 prefixEnd_785431 := by exact prefixLift 785431
  have htrace : WordTrace (prefixWord ++ tailWord_785431) baseStart_785431 baseEnd_785431 := by
    simpa [prefixWord, tailWord_785431, baseEnd_785431] using wordTrace_append hprefix tailTrace_785431
  have hstable : (prefixWord ++ tailWord_785431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785431).length < 2 ^ (prefixWord ++ tailWord_785431).sum := by decide
  have hdescent : baseEnd_785431 < baseStart_785431 := by decide
  rcases family_descends (prefixWord ++ tailWord_785431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785445 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_785445 : Nat := 118140960795 + 785445 * 2 ^ 59
def prefixEnd_785445 : Nat := 4983230072969 + 3 ^ 40 * 785445 * 2
def baseEnd_785445 : Nat := 358498500151808601355831

theorem tailTrace_785445 : CollatzResearch.WordTrace tailWord_785445 prefixEnd_785445 358498500151808601355831 := by
  unfold tailWord_785445
  simp only [CollatzResearch.WordTrace]
  refine ⟨28647532639474383171413789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19098355092982922114275859 28647532639474383171413789)
  ·
    refine ⟨10742824739802893689280171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28647532639474383171413789 10742824739802893689280171)
    ·
      refine ⟨16114237109704340533920257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742824739802893689280171 16114237109704340533920257)
      ·
        refine ⟨12085677832278255400440193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16114237109704340533920257 12085677832278255400440193)
        ·
          refine ⟨9064258374208691550330145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12085677832278255400440193 9064258374208691550330145)
          ·
            refine ⟨6798193780656518662747609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9064258374208691550330145 6798193780656518662747609)
            ·
              refine ⟨5098645335492388997060707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6798193780656518662747609 5098645335492388997060707)
              ·
                refine ⟨7647968003238583495591061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098645335492388997060707 7647968003238583495591061)
                ·
                  refine ⟨358498500151808601355831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7647968003238583495591061 358498500151808601355831)
                  ·
                    rfl

theorem cell20_785445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_785445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785445 prefixEnd_785445 := by exact prefixLift 785445
  have htrace : WordTrace (prefixWord ++ tailWord_785445) baseStart_785445 baseEnd_785445 := by
    simpa [prefixWord, tailWord_785445, baseEnd_785445] using wordTrace_append hprefix tailTrace_785445
  have hstable : (prefixWord ++ tailWord_785445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785445).length < 2 ^ (prefixWord ++ tailWord_785445).sum := by decide
  have hdescent : baseEnd_785445 < baseStart_785445 := by decide
  rcases family_descends (prefixWord ++ tailWord_785445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785452 : List Nat := [2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_785452 : Nat := 118140960795 + 785452 * 2 ^ 59
def prefixEnd_785452 : Nat := 4983230072969 + 3 ^ 40 * 785452 * 2
def baseEnd_785452 : Nat := 119500565047515896040823

theorem tailTrace_785452 : CollatzResearch.WordTrace tailWord_785452 prefixEnd_785452 119500565047515896040823 := by
  unfold tailWord_785452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14323893975224511683459305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19098525300299348911279073 14323893975224511683459305)
  ·
    refine ⟨10742920481418383762594479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14323893975224511683459305 10742920481418383762594479)
    ·
      refine ⟨16114380722127575643891719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742920481418383762594479 16114380722127575643891719)
      ·
        refine ⟨24171571083191363465837579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16114380722127575643891719 24171571083191363465837579)
        ·
          refine ⟨36257356624787045198756369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24171571083191363465837579 36257356624787045198756369)
          ·
            refine ⟨27193017468590283899067277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36257356624787045198756369 27193017468590283899067277)
            ·
              refine ⟨10197381550721356462150229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27193017468590283899067277 10197381550721356462150229)
              ·
                refine ⟨119500565047515896040823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10197381550721356462150229 119500565047515896040823)
                ·
                  rfl

theorem cell20_785452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_785452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785452 prefixEnd_785452 := by exact prefixLift 785452
  have htrace : WordTrace (prefixWord ++ tailWord_785452) baseStart_785452 baseEnd_785452 := by
    simpa [prefixWord, tailWord_785452, baseEnd_785452] using wordTrace_append hprefix tailTrace_785452
  have hstable : (prefixWord ++ tailWord_785452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785452).length < 2 ^ (prefixWord ++ tailWord_785452).sum := by decide
  have hdescent : baseEnd_785452 < baseStart_785452 := by decide
  rcases family_descends (prefixWord ++ tailWord_785452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785479 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 2]
def baseStart_785479 : Nat := 118140960795 + 785479 * 2 ^ 59
def prefixEnd_785479 : Nat := 4983230072969 + 3 ^ 40 * 785479 * 2
def baseEnd_785479 : Nat := 358514018678255594222359

theorem tailTrace_785479 : CollatzResearch.WordTrace tailWord_785479 prefixEnd_785479 358514018678255594222359 := by
  unfold tailWord_785479
  simp only [CollatzResearch.WordTrace]
  refine ⟨28648772721351206978151491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19099181814234137985434327 28648772721351206978151491)
  ·
    refine ⟨42973159082026810467227237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28648772721351206978151491 42973159082026810467227237)
    ·
      refine ⟨8057467327880026962605107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42973159082026810467227237 8057467327880026962605107)
      ·
        refine ⟨12086200991820040443907661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8057467327880026962605107 12086200991820040443907661)
        ·
          refine ⟨4532325371932515166465373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12086200991820040443907661 4532325371932515166465373)
          ·
            refine ⟨1699622014474693187424515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4532325371932515166465373 1699622014474693187424515)
            ·
              refine ⟨2549433021712039781136773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699622014474693187424515 2549433021712039781136773)
              ·
                refine ⟨478018691571007458963145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2549433021712039781136773 478018691571007458963145)
                ·
                  refine ⟨358514018678255594222359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478018691571007458963145 358514018678255594222359)
                  ·
                    rfl

theorem cell20_785479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 2].length) (baseStart_785479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785479 prefixEnd_785479 := by exact prefixLift 785479
  have htrace : WordTrace (prefixWord ++ tailWord_785479) baseStart_785479 baseEnd_785479 := by
    simpa [prefixWord, tailWord_785479, baseEnd_785479] using wordTrace_append hprefix tailTrace_785479
  have hstable : (prefixWord ++ tailWord_785479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785479).length < 2 ^ (prefixWord ++ tailWord_785479).sum := by decide
  have hdescent : baseEnd_785479 < baseStart_785479 := by decide
  rcases family_descends (prefixWord ++ tailWord_785479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785500 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_785500 : Nat := 118140960795 + 785500 * 2 ^ 59
def prefixEnd_785500 : Nat := 4983230072969 + 3 ^ 40 * 785500 * 2
def baseEnd_785500 : Nat := 358523603650472854522273

theorem tailTrace_785500 : CollatzResearch.WordTrace tailWord_785500 prefixEnd_785500 358523603650472854522273 := by
  unfold tailWord_785500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14324769327137563782332977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19099692436183418376443969 14324769327137563782332977)
  ·
    refine ⟨10743576995353172836749733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14324769327137563782332977 10743576995353172836749733)
    ·
      refine ⟨2014420686628719906890575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10743576995353172836749733 2014420686628719906890575)
      ·
        refine ⟨3021631029943079860335863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014420686628719906890575 3021631029943079860335863)
        ·
          refine ⟨4532446544914619790503795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021631029943079860335863 4532446544914619790503795)
          ·
            refine ⟨6798669817371929685755693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532446544914619790503795 6798669817371929685755693)
            ·
              refine ⟨2549501181514473632158385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6798669817371929685755693 2549501181514473632158385)
              ·
                refine ⟨1912125886135855224118789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549501181514473632158385 1912125886135855224118789)
                ·
                  refine ⟨358523603650472854522273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912125886135855224118789 358523603650472854522273)
                  ·
                    rfl

theorem cell20_785500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_785500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785500 prefixEnd_785500 := by exact prefixLift 785500
  have htrace : WordTrace (prefixWord ++ tailWord_785500) baseStart_785500 baseEnd_785500 := by
    simpa [prefixWord, tailWord_785500, baseEnd_785500] using wordTrace_append hprefix tailTrace_785500
  have hstable : (prefixWord ++ tailWord_785500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785500).length < 2 ^ (prefixWord ++ tailWord_785500).sum := by decide
  have hdescent : baseEnd_785500 < baseStart_785500 := by decide
  rcases family_descends (prefixWord ++ tailWord_785500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785517 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 2]
def baseStart_785517 : Nat := 118140960795 + 785517 * 2 ^ 59
def prefixEnd_785517 : Nat := 4983230072969 + 3 ^ 40 * 785517 * 2
def baseEnd_785517 : Nat := 358531362913696350955537

theorem tailTrace_785517 : CollatzResearch.WordTrace tailWord_785517 prefixEnd_785517 358531362913696350955537 := by
  unfold tailWord_785517
  simp only [CollatzResearch.WordTrace]
  refine ⟨28650158695213539468034805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19100105796809026312023203 28650158695213539468034805)
  ·
    refine ⟨2685952377676269325128263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28650158695213539468034805 2685952377676269325128263)
    ·
      refine ⟨4028928566514403987692395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685952377676269325128263 4028928566514403987692395)
      ·
        refine ⟨6043392849771605981538593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4028928566514403987692395 6043392849771605981538593)
        ·
          refine ⟨4532544637328704486153945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6043392849771605981538593 4532544637328704486153945)
          ·
            refine ⟨3399408477996528364615459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4532544637328704486153945 3399408477996528364615459)
            ·
              refine ⟨5099112716994792546923189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399408477996528364615459 5099112716994792546923189)
              ·
                refine ⟨478041817218261801274049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5099112716994792546923189 478041817218261801274049)
                ·
                  refine ⟨358531362913696350955537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478041817218261801274049 358531362913696350955537)
                  ·
                    rfl

theorem cell20_785517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_785517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785517 prefixEnd_785517 := by exact prefixLift 785517
  have htrace : WordTrace (prefixWord ++ tailWord_785517) baseStart_785517 baseEnd_785517 := by
    simpa [prefixWord, tailWord_785517, baseEnd_785517] using wordTrace_append hprefix tailTrace_785517
  have hstable : (prefixWord ++ tailWord_785517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785517).length < 2 ^ (prefixWord ++ tailWord_785517).sum := by decide
  have hdescent : baseEnd_785517 < baseStart_785517 := by decide
  rcases family_descends (prefixWord ++ tailWord_785517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785562 : List Nat := [3, 1, 1, 5, 1, 1, 4, 4]
def baseStart_785562 : Nat := 118140960795 + 785562 * 2 ^ 59
def prefixEnd_785562 : Nat := 4983230072969 + 3 ^ 40 * 785562 * 2
def baseEnd_785562 : Nat := 119517300713292064818451

theorem tailTrace_785562 : CollatzResearch.WordTrace tailWord_785562 prefixEnd_785562 119517300713292064818451 := by
  unfold tailWord_785562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7162949995012628038355735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19101199986700341435615293 7162949995012628038355735)
  ·
    refine ⟨10744424992518942057533603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7162949995012628038355735 10744424992518942057533603)
    ·
      refine ⟨16116637488778413086300405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10744424992518942057533603 16116637488778413086300405)
      ·
        refine ⟨1510934764572976226840663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16116637488778413086300405 1510934764572976226840663)
        ·
          refine ⟨2266402146859464340260995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510934764572976226840663 2266402146859464340260995)
          ·
            refine ⟨3399603220289196510391493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266402146859464340260995 3399603220289196510391493)
            ·
              refine ⟨637425603804224345698405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3399603220289196510391493 637425603804224345698405)
              ·
                refine ⟨119517300713292064818451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637425603804224345698405 119517300713292064818451)
                ·
                  rfl

theorem cell20_785562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_785562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785562 prefixEnd_785562 := by exact prefixLift 785562
  have htrace : WordTrace (prefixWord ++ tailWord_785562) baseStart_785562 baseEnd_785562 := by
    simpa [prefixWord, tailWord_785562, baseEnd_785562] using wordTrace_append hprefix tailTrace_785562
  have hstable : (prefixWord ++ tailWord_785562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785562).length < 2 ^ (prefixWord ++ tailWord_785562).sum := by decide
  have hdescent : baseEnd_785562 < baseStart_785562 := by decide
  rcases family_descends (prefixWord ++ tailWord_785562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785572 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 2]
def baseStart_785572 : Nat := 118140960795 + 785572 * 2 ^ 59
def prefixEnd_785572 : Nat := 4983230072969 + 3 ^ 40 * 785572 * 2
def baseEnd_785572 : Nat := 358556466412360604121979

theorem tailTrace_785572 : CollatzResearch.WordTrace tailWord_785572 prefixEnd_785572 358556466412360604121979 := by
  unfold tailWord_785572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14326082355007141930643485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19101443140009522574191313 14326082355007141930643485)
  ·
    refine ⟨5372280883127678223991307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14326082355007141930643485 5372280883127678223991307)
    ·
      refine ⟨8058421324691517335986961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372280883127678223991307 8058421324691517335986961)
      ·
        refine ⟨6043815993518638001990221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8058421324691517335986961 6043815993518638001990221)
        ·
          refine ⟨2266430997569489250746333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6043815993518638001990221 2266430997569489250746333)
          ·
            refine ⟨849911624088558469029875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2266430997569489250746333 849911624088558469029875)
            ·
              refine ⟨1274867436132837703544813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849911624088558469029875 1274867436132837703544813)
              ·
                refine ⟨478075288549814138829305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1274867436132837703544813 478075288549814138829305)
                ·
                  refine ⟨358556466412360604121979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478075288549814138829305 358556466412360604121979)
                  ·
                    rfl

theorem cell20_785572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_785572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785572 prefixEnd_785572 := by exact prefixLift 785572
  have htrace : WordTrace (prefixWord ++ tailWord_785572) baseStart_785572 baseEnd_785572 := by
    simpa [prefixWord, tailWord_785572, baseEnd_785572] using wordTrace_append hprefix tailTrace_785572
  have hstable : (prefixWord ++ tailWord_785572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785572).length < 2 ^ (prefixWord ++ tailWord_785572).sum := by decide
  have hdescent : baseEnd_785572 < baseStart_785572 := by decide
  rcases family_descends (prefixWord ++ tailWord_785572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785611 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_785611 : Nat := 118140960795 + 785611 * 2 ^ 59
def prefixEnd_785611 : Nat := 4983230072969 + 3 ^ 40 * 785611 * 2
def baseEnd_785611 : Nat := 358574267075049801821819

theorem tailTrace_785611 : CollatzResearch.WordTrace tailWord_785611 prefixEnd_785611 358574267075049801821819 := by
  unfold tailWord_785611
  simp only [CollatzResearch.WordTrace]
  refine ⟨28653587156872993521956687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19102391437915329014637791 28653587156872993521956687)
  ·
    refine ⟨42980380735309490282935031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28653587156872993521956687 42980380735309490282935031)
    ·
      refine ⟨64470571102964235424402547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42980380735309490282935031 64470571102964235424402547)
      ·
        refine ⟨96705856654446353136603821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64470571102964235424402547 96705856654446353136603821)
        ·
          refine ⟨36264696245417382426226433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96705856654446353136603821 36264696245417382426226433)
          ·
            refine ⟨27198522184063036819669825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36264696245417382426226433 27198522184063036819669825)
            ·
              refine ⟨20398891638047277614752369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27198522184063036819669825 20398891638047277614752369)
              ·
                refine ⟨15299168728535458211064277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20398891638047277614752369 15299168728535458211064277)
                ·
                  refine ⟨358574267075049801821819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15299168728535458211064277 358574267075049801821819)
                  ·
                    rfl

theorem cell20_785611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_785611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785611 prefixEnd_785611 := by exact prefixLift 785611
  have htrace : WordTrace (prefixWord ++ tailWord_785611) baseStart_785611 baseEnd_785611 := by
    simpa [prefixWord, tailWord_785611, baseEnd_785611] using wordTrace_append hprefix tailTrace_785611
  have hstable : (prefixWord ++ tailWord_785611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785611).length < 2 ^ (prefixWord ++ tailWord_785611).sum := by decide
  have hdescent : baseEnd_785611 < baseStart_785611 := by decide
  rcases family_descends (prefixWord ++ tailWord_785611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785621 : List Nat := [1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_785621 : Nat := 118140960795 + 785621 * 2 ^ 59
def prefixEnd_785621 : Nat := 4983230072969 + 3 ^ 40 * 785621 * 2
def baseEnd_785621 : Nat := 119526277115844737162815

theorem tailTrace_785621 : CollatzResearch.WordTrace tailWord_785621 prefixEnd_785621 119526277115844737162815 := by
  unfold tailWord_785621
  simp only [CollatzResearch.WordTrace]
  refine ⟨28653951886836765229820717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19102634591224510153213811 28653951886836765229820717)
  ·
    refine ⟨10745231957563786961182769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28653951886836765229820717 10745231957563786961182769)
    ·
      refine ⟨8058923968172840220887077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10745231957563786961182769 8058923968172840220887077)
      ·
        refine ⟨1511048244032407541416327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8058923968172840220887077 1511048244032407541416327)
        ·
          refine ⟨2266572366048611312124491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511048244032407541416327 2266572366048611312124491)
          ·
            refine ⟨3399858549072916968186737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266572366048611312124491 3399858549072916968186737)
            ·
              refine ⟨2549893911804687726140053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399858549072916968186737 2549893911804687726140053)
              ·
                refine ⟨119526277115844737162815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2549893911804687726140053 119526277115844737162815)
                ·
                  rfl

theorem cell20_785621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_785621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785621 prefixEnd_785621 := by exact prefixLift 785621
  have htrace : WordTrace (prefixWord ++ tailWord_785621) baseStart_785621 baseEnd_785621 := by
    simpa [prefixWord, tailWord_785621, baseEnd_785621] using wordTrace_append hprefix tailTrace_785621
  have hstable : (prefixWord ++ tailWord_785621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785621).length < 2 ^ (prefixWord ++ tailWord_785621).sum := by decide
  have hdescent : baseEnd_785621 < baseStart_785621 := by decide
  rcases family_descends (prefixWord ++ tailWord_785621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785642 : List Nat := [3, 1, 3, 1, 1, 11]
def baseStart_785642 : Nat := 118140960795 + 785642 * 2 ^ 59
def prefixEnd_785642 : Nat := 4983230072969 + 3 ^ 40 * 785642 * 2
def baseEnd_785642 : Nat := 13281052456287091547717

theorem tailTrace_785642 : CollatzResearch.WordTrace tailWord_785642 prefixEnd_785642 13281052456287091547717 := by
  unfold tailWord_785642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163679454940171454083795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19103145213173790544223453 7163679454940171454083795)
  ·
    refine ⟨10745519182410257181125693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7163679454940171454083795 10745519182410257181125693)
    ·
      refine ⟨4029569693403846442922135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10745519182410257181125693 4029569693403846442922135)
      ·
        refine ⟨6044354540105769664383203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029569693403846442922135 6044354540105769664383203)
        ·
          refine ⟨9066531810158654496574805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044354540105769664383203 9066531810158654496574805)
          ·
            refine ⟨13281052456287091547717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9066531810158654496574805 13281052456287091547717)
            ·
              rfl

theorem cell20_785642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 11].length) (baseStart_785642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785642 prefixEnd_785642 := by exact prefixLift 785642
  have htrace : WordTrace (prefixWord ++ tailWord_785642) baseStart_785642 baseEnd_785642 := by
    simpa [prefixWord, tailWord_785642, baseEnd_785642] using wordTrace_append hprefix tailTrace_785642
  have hstable : (prefixWord ++ tailWord_785642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785642).length < 2 ^ (prefixWord ++ tailWord_785642).sum := by decide
  have hdescent : baseEnd_785642 < baseStart_785642 := by decide
  rcases family_descends (prefixWord ++ tailWord_785642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785645 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_785645 : Nat := 118140960795 + 785645 * 2 ^ 59
def prefixEnd_785645 : Nat := 4983230072969 + 3 ^ 40 * 785645 * 2
def baseEnd_785645 : Nat := 358589785601496794688347

theorem tailTrace_785645 : CollatzResearch.WordTrace tailWord_785645 prefixEnd_785645 358589785601496794688347 := by
  unfold tailWord_785645
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654827238749817328694389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19103218159166544885796259 28654827238749817328694389)
  ·
    refine ⟨2686390053632795374565099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28654827238749817328694389 2686390053632795374565099)
    ·
      refine ⟨4029585080449193061847649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686390053632795374565099 4029585080449193061847649)
      ·
        refine ⟨3022188810336894796385737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029585080449193061847649 3022188810336894796385737)
        ·
          refine ⟨2266641607752671097289303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022188810336894796385737 2266641607752671097289303)
          ·
            refine ⟨3399962411629006645933955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266641607752671097289303 3399962411629006645933955)
            ·
              refine ⟨5099943617443509968900933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399962411629006645933955 5099943617443509968900933)
              ·
                refine ⟨956239428270658119168925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5099943617443509968900933 956239428270658119168925)
                ·
                  refine ⟨358589785601496794688347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956239428270658119168925 358589785601496794688347)
                  ·
                    rfl

theorem cell20_785645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_785645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785645 prefixEnd_785645 := by exact prefixLift 785645
  have htrace : WordTrace (prefixWord ++ tailWord_785645) baseStart_785645 baseEnd_785645 := by
    simpa [prefixWord, tailWord_785645, baseEnd_785645] using wordTrace_append hprefix tailTrace_785645
  have hstable : (prefixWord ++ tailWord_785645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785645).length < 2 ^ (prefixWord ++ tailWord_785645).sum := by decide
  have hdescent : baseEnd_785645 < baseStart_785645 := by decide
  rcases family_descends (prefixWord ++ tailWord_785645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785673 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_785673 : Nat := 118140960795 + 785673 * 2 ^ 59
def prefixEnd_785673 : Nat := 4983230072969 + 3 ^ 40 * 785673 * 2
def baseEnd_785673 : Nat := 358602565564453141754899

theorem tailTrace_785673 : CollatzResearch.WordTrace tailWord_785673 prefixEnd_785673 358602565564453141754899 := by
  unfold tailWord_785673
  simp only [CollatzResearch.WordTrace]
  refine ⟨28655848482648378110713673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19103898988432252073809115 28655848482648378110713673)
  ·
    refine ⟨21491886361986283583035255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28655848482648378110713673 21491886361986283583035255)
    ·
      refine ⟨32237829542979425374552883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21491886361986283583035255 32237829542979425374552883)
      ·
        refine ⟨48356744314469138061829325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32237829542979425374552883 48356744314469138061829325)
        ·
          refine ⟨18133779117925926773185997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48356744314469138061829325 18133779117925926773185997)
          ·
            refine ⟨6800167169222222539944749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18133779117925926773185997 6800167169222222539944749)
            ·
              refine ⟨2550062688458333452479281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6800167169222222539944749 2550062688458333452479281)
              ·
                refine ⟨1912547016343750089359461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550062688458333452479281 1912547016343750089359461)
                ·
                  refine ⟨358602565564453141754899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912547016343750089359461 358602565564453141754899)
                  ·
                    rfl

theorem cell20_785673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_785673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785673 prefixEnd_785673 := by exact prefixLift 785673
  have htrace : WordTrace (prefixWord ++ tailWord_785673) baseStart_785673 baseEnd_785673 := by
    simpa [prefixWord, tailWord_785673, baseEnd_785673] using wordTrace_append hprefix tailTrace_785673
  have hstable : (prefixWord ++ tailWord_785673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785673).length < 2 ^ (prefixWord ++ tailWord_785673).sum := by decide
  have hdescent : baseEnd_785673 < baseStart_785673 := by decide
  rcases family_descends (prefixWord ++ tailWord_785673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785735 : List Nat := [1, 1, 4, 1, 2, 3, 4, 4]
def baseStart_785735 : Nat := 118140960795 + 785735 * 2 ^ 59
def prefixEnd_785735 : Nat := 4983230072969 + 3 ^ 40 * 785735 * 2
def baseEnd_785735 : Nat := 119543621351285493895993

theorem tailTrace_785735 : CollatzResearch.WordTrace tailWord_785735 prefixEnd_785735 119543621351285493895993 := by
  unfold tailWord_785735
  simp only [CollatzResearch.WordTrace]
  refine ⟨28658109808423762699470659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19105406538949175132980439 28658109808423762699470659)
  ·
    refine ⟨42987164712635644049205989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28658109808423762699470659 42987164712635644049205989)
    ·
      refine ⟨8060093383619183259226123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42987164712635644049205989 8060093383619183259226123)
      ·
        refine ⟨12090140075428774888839185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060093383619183259226123 12090140075428774888839185)
        ·
          refine ⟨9067605056571581166629389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12090140075428774888839185 9067605056571581166629389)
          ·
            refine ⟨3400351896214342937486021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9067605056571581166629389 3400351896214342937486021)
            ·
              refine ⟨637565980540189300778629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3400351896214342937486021 637565980540189300778629)
              ·
                refine ⟨119543621351285493895993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637565980540189300778629 119543621351285493895993)
                ·
                  rfl

theorem cell20_785735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_785735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785735 prefixEnd_785735 := by exact prefixLift 785735
  have htrace : WordTrace (prefixWord ++ tailWord_785735) baseStart_785735 baseEnd_785735 := by
    simpa [prefixWord, tailWord_785735, baseEnd_785735] using wordTrace_append hprefix tailTrace_785735
  have hstable : (prefixWord ++ tailWord_785735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785735).length < 2 ^ (prefixWord ++ tailWord_785735).sum := by decide
  have hdescent : baseEnd_785735 < baseStart_785735 := by decide
  rcases family_descends (prefixWord ++ tailWord_785735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785762 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_785762 : Nat := 118140960795 + 785762 * 2 ^ 59
def prefixEnd_785762 : Nat := 4983230072969 + 3 ^ 40 * 785762 * 2
def baseEnd_785762 : Nat := 358643187589564387787869

theorem tailTrace_785762 : CollatzResearch.WordTrace tailWord_785762 prefixEnd_785762 358643187589564387787869 := by
  unfold tailWord_785762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164773644831486577675885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19106063052883964207135693 7164773644831486577675885)
  ·
    refine ⟨2686790116811807466628457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7164773644831486577675885 2686790116811807466628457)
    ·
      refine ⟨2015092587608855599971343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2686790116811807466628457 2015092587608855599971343)
      ·
        refine ⟨3022638881413283399957015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015092587608855599971343 3022638881413283399957015)
        ·
          refine ⟨4533958322119925099935523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022638881413283399957015 4533958322119925099935523)
          ·
            refine ⟨6800937483179887649903285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533958322119925099935523 6800937483179887649903285)
            ·
              refine ⟨637587889048114467178433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6800937483179887649903285 637587889048114467178433)
              ·
                refine ⟨478190916786085850383825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637587889048114467178433 478190916786085850383825)
                ·
                  refine ⟨358643187589564387787869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478190916786085850383825 358643187589564387787869)
                  ·
                    rfl

theorem cell20_785762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_785762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785762 prefixEnd_785762 := by exact prefixLift 785762
  have htrace : WordTrace (prefixWord ++ tailWord_785762) baseStart_785762 baseEnd_785762 := by
    simpa [prefixWord, tailWord_785762, baseEnd_785762] using wordTrace_append hprefix tailTrace_785762
  have hstable : (prefixWord ++ tailWord_785762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785762).length < 2 ^ (prefixWord ++ tailWord_785762).sum := by decide
  have hdescent : baseEnd_785762 < baseStart_785762 := by decide
  rcases family_descends (prefixWord ++ tailWord_785762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785773 : List Nat := [1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_785773 : Nat := 118140960795 + 785773 * 2 ^ 59
def prefixEnd_785773 : Nat := 4983230072969 + 3 ^ 40 * 785773 * 2
def baseEnd_785773 : Nat := 119549402763099079473719

theorem tailTrace_785773 : CollatzResearch.WordTrace tailWord_785773 prefixEnd_785773 119549402763099079473719 := by
  unfold tailWord_785773
  simp only [CollatzResearch.WordTrace]
  refine ⟨28659495782286095189353973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19106330521524063459569315 28659495782286095189353973)
  ·
    refine ⟨2686827729589321424001935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28659495782286095189353973 2686827729589321424001935)
    ·
      refine ⟨4030241594383982136002903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686827729589321424001935 4030241594383982136002903)
      ·
        refine ⟨6045362391575973204004355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030241594383982136002903 6045362391575973204004355)
        ·
          refine ⟨9068043587363959806006533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045362391575973204004355 9068043587363959806006533)
          ·
            refine ⟨1700258172630742463626225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9068043587363959806006533 1700258172630742463626225)
            ·
              refine ⟨1275193629473056847719669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700258172630742463626225 1275193629473056847719669)
              ·
                refine ⟨119549402763099079473719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1275193629473056847719669 119549402763099079473719)
                ·
                  rfl

theorem cell20_785773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_785773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785773 prefixEnd_785773 := by exact prefixLift 785773
  have htrace : WordTrace (prefixWord ++ tailWord_785773) baseStart_785773 baseEnd_785773 := by
    simpa [prefixWord, tailWord_785773, baseEnd_785773] using wordTrace_append hprefix tailTrace_785773
  have hstable : (prefixWord ++ tailWord_785773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785773).length < 2 ^ (prefixWord ++ tailWord_785773).sum := by decide
  have hdescent : baseEnd_785773 < baseStart_785773 := by decide
  rcases family_descends (prefixWord ++ tailWord_785773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785804 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 2]
def baseStart_785804 : Nat := 118140960795 + 785804 * 2 ^ 59
def prefixEnd_785804 : Nat := 4983230072969 + 3 ^ 40 * 785804 * 2
def baseEnd_785804 : Nat := 358662357533998908387697

theorem tailTrace_785804 : CollatzResearch.WordTrace tailWord_785804 prefixEnd_785804 358662357533998908387697 := by
  unfold tailWord_785804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330313222586893741866233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19107084296782524989154977 14330313222586893741866233)
  ·
    refine ⟨10747734916940170306399675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14330313222586893741866233 10747734916940170306399675)
    ·
      refine ⟨16121602375410255459599513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10747734916940170306399675 16121602375410255459599513)
      ·
        refine ⟨12091201781557691594699635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16121602375410255459599513 12091201781557691594699635)
        ·
          refine ⟨18136802672336537392049453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12091201781557691594699635 18136802672336537392049453)
          ·
            refine ⟨6801301002126201522018545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18136802672336537392049453 6801301002126201522018545)
            ·
              refine ⟨5100975751594651141513909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6801301002126201522018545 5100975751594651141513909)
              ·
                refine ⟨478216476711998544516929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5100975751594651141513909 478216476711998544516929)
                ·
                  refine ⟨358662357533998908387697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478216476711998544516929 358662357533998908387697)
                  ·
                    rfl

theorem cell20_785804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_785804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785804 prefixEnd_785804 := by exact prefixLift 785804
  have htrace : WordTrace (prefixWord ++ tailWord_785804) baseStart_785804 baseEnd_785804 := by
    simpa [prefixWord, tailWord_785804, baseEnd_785804] using wordTrace_append hprefix tailTrace_785804
  have hstable : (prefixWord ++ tailWord_785804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785804).length < 2 ^ (prefixWord ++ tailWord_785804).sum := by decide
  have hdescent : baseEnd_785804 < baseStart_785804 := by decide
  rcases family_descends (prefixWord ++ tailWord_785804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785821 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 2]
def baseStart_785821 : Nat := 118140960795 + 785821 * 2 ^ 59
def prefixEnd_785821 : Nat := 4983230072969 + 3 ^ 40 * 785821 * 2
def baseEnd_785821 : Nat := 358670116797222404820961

theorem tailTrace_785821 : CollatzResearch.WordTrace tailWord_785821 prefixEnd_785821 358670116797222404820961 := by
  unfold tailWord_785821
  simp only [CollatzResearch.WordTrace]
  refine ⟨28661246486112199387101317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19107497657408132924734211 28661246486112199387101317)
  ·
    refine ⟨5373983716146037385081497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28661246486112199387101317 5373983716146037385081497)
    ·
      refine ⟨4030487787109528038811123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5373983716146037385081497 4030487787109528038811123)
      ·
        refine ⟨6045731680664292058216685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030487787109528038811123 6045731680664292058216685)
        ·
          refine ⟨2267149380249109521831257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6045731680664292058216685 2267149380249109521831257)
          ·
            refine ⟨1700362035186832141373443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2267149380249109521831257 1700362035186832141373443)
            ·
              refine ⟨2550543052780248212060165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700362035186832141373443 2550543052780248212060165)
              ·
                refine ⟨478226822396296539761281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2550543052780248212060165 478226822396296539761281)
                ·
                  refine ⟨358670116797222404820961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478226822396296539761281 358670116797222404820961)
                  ·
                    rfl

theorem cell20_785821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_785821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785821 prefixEnd_785821 := by exact prefixLift 785821
  have htrace : WordTrace (prefixWord ++ tailWord_785821) baseStart_785821 baseEnd_785821 := by
    simpa [prefixWord, tailWord_785821, baseEnd_785821] using wordTrace_append hprefix tailTrace_785821
  have hstable : (prefixWord ++ tailWord_785821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785821).length < 2 ^ (prefixWord ++ tailWord_785821).sum := by decide
  have hdescent : baseEnd_785821 < baseStart_785821 := by decide
  rcases family_descends (prefixWord ++ tailWord_785821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785880 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 2]
def baseStart_785880 : Nat := 118140960795 + 785880 * 2 ^ 59
def prefixEnd_785880 : Nat := 4983230072969 + 3 ^ 40 * 785880 * 2
def baseEnd_785880 : Nat := 358697046004880421854053

theorem tailTrace_785880 : CollatzResearch.WordTrace tailWord_785880 prefixEnd_785880 358697046004880421854053 := by
  unfold tailWord_785880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331699196449226231749547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19108932261932301642332729 14331699196449226231749547)
  ·
    refine ⟨21497548794673839347624321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14331699196449226231749547 21497548794673839347624321)
    ·
      refine ⟨16123161596005379510718241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21497548794673839347624321 16123161596005379510718241)
      ·
        refine ⟨12092371197004034633038681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16123161596005379510718241 12092371197004034633038681)
        ·
          refine ⟨9069278397753025974779011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12092371197004034633038681 9069278397753025974779011)
          ·
            refine ⟨13603917596629538962168517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069278397753025974779011 13603917596629538962168517)
            ·
              refine ⟨2550734549368038555406597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13603917596629538962168517 2550734549368038555406597)
              ·
                refine ⟨478262728006507229138737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2550734549368038555406597 478262728006507229138737)
                ·
                  refine ⟨358697046004880421854053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478262728006507229138737 358697046004880421854053)
                  ·
                    rfl

theorem cell20_785880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_785880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785880 prefixEnd_785880 := by exact prefixLift 785880
  have htrace : WordTrace (prefixWord ++ tailWord_785880) baseStart_785880 baseEnd_785880 := by
    simpa [prefixWord, tailWord_785880, baseEnd_785880] using wordTrace_append hprefix tailTrace_785880
  have hstable : (prefixWord ++ tailWord_785880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785880).length < 2 ^ (prefixWord ++ tailWord_785880).sum := by decide
  have hdescent : baseEnd_785880 < baseStart_785880 := by decide
  rcases family_descends (prefixWord ++ tailWord_785880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785939 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_785939 : Nat := 118140960795 + 785939 * 2 ^ 59
def prefixEnd_785939 : Nat := 4983230072969 + 3 ^ 40 * 785939 * 2
def baseEnd_785939 : Nat := 358723975212538438887145

theorem tailTrace_785939 : CollatzResearch.WordTrace tailWord_785939 prefixEnd_785939 358723975212538438887145 := by
  unfold tailWord_785939
  simp only [CollatzResearch.WordTrace]
  refine ⟨28665550299684705539896871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19110366866456470359931247 28665550299684705539896871)
  ·
    refine ⟨42998325449527058309845307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28665550299684705539896871 42998325449527058309845307)
    ·
      refine ⟨64497488174290587464767961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42998325449527058309845307 64497488174290587464767961)
      ·
        refine ⟨48373116130717940598575971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64497488174290587464767961 48373116130717940598575971)
        ·
          refine ⟨72559674196076910897863957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48373116130717940598575971 72559674196076910897863957)
          ·
            refine ⟨3401234727941105198337373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72559674196076910897863957 3401234727941105198337373)
            ·
              refine ⟨1275463022977914449376515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3401234727941105198337373 1275463022977914449376515)
              ·
                refine ⟨1913194534466871674064773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275463022977914449376515 1913194534466871674064773)
                ·
                  refine ⟨358723975212538438887145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913194534466871674064773 358723975212538438887145)
                  ·
                    rfl

theorem cell20_785939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_785939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785939 prefixEnd_785939 := by exact prefixLift 785939
  have htrace : WordTrace (prefixWord ++ tailWord_785939) baseStart_785939 baseEnd_785939 := by
    simpa [prefixWord, tailWord_785939, baseEnd_785939] using wordTrace_append hprefix tailTrace_785939
  have hstable : (prefixWord ++ tailWord_785939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785939).length < 2 ^ (prefixWord ++ tailWord_785939).sum := by decide
  have hdescent : baseEnd_785939 < baseStart_785939 := by decide
  rcases family_descends (prefixWord ++ tailWord_785939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785994 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_785994 : Nat := 118140960795 + 785994 * 2 ^ 59
def prefixEnd_785994 : Nat := 4983230072969 + 3 ^ 40 * 785994 * 2
def baseEnd_785994 : Nat := 358749078711202692053587

theorem tailTrace_785994 : CollatzResearch.WordTrace tailWord_785994 prefixEnd_785994 358749078711202692053587 := by
  unfold tailWord_785994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166889078621362483287259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19111704209656966622099357 7166889078621362483287259)
  ·
    refine ⟨10750333617932043724930889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7166889078621362483287259 10750333617932043724930889)
    ·
      refine ⟨8062750213449032793698167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10750333617932043724930889 8062750213449032793698167)
      ·
        refine ⟨12094125320173549190547251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8062750213449032793698167 12094125320173549190547251)
        ·
          refine ⟨18141187980260323785820877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12094125320173549190547251 18141187980260323785820877)
          ·
            refine ⟨6802945492597621419682829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18141187980260323785820877 6802945492597621419682829)
            ·
              refine ⟨2551104559724108032381061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6802945492597621419682829 2551104559724108032381061)
              ·
                refine ⟨478332104948270256071449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2551104559724108032381061 478332104948270256071449)
                ·
                  refine ⟨358749078711202692053587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478332104948270256071449 358749078711202692053587)
                  ·
                    rfl

theorem cell20_785994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_785994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785994 prefixEnd_785994 := by exact prefixLift 785994
  have htrace : WordTrace (prefixWord ++ tailWord_785994) baseStart_785994 baseEnd_785994 := by
    simpa [prefixWord, tailWord_785994, baseEnd_785994] using wordTrace_append hprefix tailTrace_785994
  have hstable : (prefixWord ++ tailWord_785994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785994).length < 2 ^ (prefixWord ++ tailWord_785994).sum := by decide
  have hdescent : baseEnd_785994 < baseStart_785994 := by decide
  rcases family_descends (prefixWord ++ tailWord_785994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785997 : List Nat := [1, 6, 1, 1, 4, 1, 1, 5]
def baseStart_785997 : Nat := 118140960795 + 785997 * 2 ^ 59
def prefixEnd_785997 : Nat := 4983230072969 + 3 ^ 40 * 785997 * 2
def baseEnd_785997 : Nat := 119583482664316004984525

theorem tailTrace_785997 : CollatzResearch.WordTrace tailWord_785997 prefixEnd_785997 119583482664316004984525 := by
  unfold tailWord_785997
  simp only [CollatzResearch.WordTrace]
  refine ⟨28667665733474581445508245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19111777155649720963672163 28667665733474581445508245)
  ·
    refine ⟨1343796831256621005258199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28667665733474581445508245 1343796831256621005258199)
    ·
      refine ⟨2015695246884931507887299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343796831256621005258199 2015695246884931507887299)
      ·
        refine ⟨3023542870327397261830949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015695246884931507887299 3023542870327397261830949)
        ·
          refine ⟨566914288186386986593303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3023542870327397261830949 566914288186386986593303)
          ·
            refine ⟨850371432279580479889955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566914288186386986593303 850371432279580479889955)
            ·
              refine ⟨1275557148419370719834933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850371432279580479889955 1275557148419370719834933)
              ·
                refine ⟨119583482664316004984525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1275557148419370719834933 119583482664316004984525)
                ·
                  rfl

theorem cell20_785997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].length) (baseStart_785997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_785997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_785997 prefixEnd_785997 := by exact prefixLift 785997
  have htrace : WordTrace (prefixWord ++ tailWord_785997) baseStart_785997 baseEnd_785997 := by
    simpa [prefixWord, tailWord_785997, baseEnd_785997] using wordTrace_append hprefix tailTrace_785997
  have hstable : (prefixWord ++ tailWord_785997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785997).length < 2 ^ (prefixWord ++ tailWord_785997).sum := by decide
  have hdescent : baseEnd_785997 < baseStart_785997 := by decide
  rcases family_descends (prefixWord ++ tailWord_785997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786032 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 2]
def baseStart_786032 : Nat := 118140960795 + 786032 * 2 ^ 59
def prefixEnd_786032 : Nat := 4983230072969 + 3 ^ 40 * 786032 * 2
def baseEnd_786032 : Nat := 358766422946643448786765

theorem tailTrace_786032 : CollatzResearch.WordTrace tailWord_786032 prefixEnd_786032 358766422946643448786765 := by
  unfold tailWord_786032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14334471144173891211516175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19112628192231854948688233 14334471144173891211516175)
  ·
    refine ⟨21501706716260836817274263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14334471144173891211516175 21501706716260836817274263)
    ·
      refine ⟨32252560074391255225911395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21501706716260836817274263 32252560074391255225911395)
      ·
        refine ⟨48378840111586882838867093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32252560074391255225911395 48378840111586882838867093)
        ·
          refine ⟨2267758130230635133071895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48378840111586882838867093 2267758130230635133071895)
          ·
            refine ⟨3401637195345952699607843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267758130230635133071895 3401637195345952699607843)
            ·
              refine ⟨5102455793018929049411765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401637195345952699607843 5102455793018929049411765)
              ·
                refine ⟨478355230595524598382353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5102455793018929049411765 478355230595524598382353)
                ·
                  refine ⟨358766422946643448786765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478355230595524598382353 358766422946643448786765)
                  ·
                    rfl

theorem cell20_786032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_786032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786032 prefixEnd_786032 := by exact prefixLift 786032
  have htrace : WordTrace (prefixWord ++ tailWord_786032) baseStart_786032 baseEnd_786032 := by
    simpa [prefixWord, tailWord_786032, baseEnd_786032] using wordTrace_append hprefix tailTrace_786032
  have hstable : (prefixWord ++ tailWord_786032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786032).length < 2 ^ (prefixWord ++ tailWord_786032).sum := by decide
  have hdescent : baseEnd_786032 < baseStart_786032 := by decide
  rcases family_descends (prefixWord ++ tailWord_786032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786043 : List Nat := [1, 1, 1, 1, 1, 4, 11]
def baseStart_786043 : Nat := 118140960795 + 786043 * 2 ^ 59
def prefixEnd_786043 : Nat := 4983230072969 + 3 ^ 40 * 786043 * 2
def baseEnd_786043 : Nat := 39863493738486255491117

theorem tailTrace_786043 : CollatzResearch.WordTrace tailWord_786043 prefixEnd_786043 39863493738486255491117 := by
  unfold tailWord_786043
  simp only [CollatzResearch.WordTrace]
  refine ⟨28669343491307931301682783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19112895660871954201121855 28669343491307931301682783)
  ·
    refine ⟨43004015236961896952524175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28669343491307931301682783 43004015236961896952524175)
    ·
      refine ⟨64506022855442845428786263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43004015236961896952524175 64506022855442845428786263)
      ·
        refine ⟨96759034283164268143179395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64506022855442845428786263 96759034283164268143179395)
        ·
          refine ⟨145138551424746402214769093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96759034283164268143179395 145138551424746402214769093)
          ·
            refine ⟨27213478392139950415269205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145138551424746402214769093 27213478392139950415269205)
            ·
              refine ⟨39863493738486255491117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27213478392139950415269205 39863493738486255491117)
              ·
                rfl

theorem cell20_786043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_786043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786043 prefixEnd_786043 := by exact prefixLift 786043
  have htrace : WordTrace (prefixWord ++ tailWord_786043) baseStart_786043 baseEnd_786043 := by
    simpa [prefixWord, tailWord_786043, baseEnd_786043] using wordTrace_append hprefix tailTrace_786043
  have hstable : (prefixWord ++ tailWord_786043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786043).length < 2 ^ (prefixWord ++ tailWord_786043).sum := by decide
  have hdescent : baseEnd_786043 < baseStart_786043 := by decide
  rcases family_descends (prefixWord ++ tailWord_786043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786053 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_786053 : Nat := 118140960795 + 786053 * 2 ^ 59
def prefixEnd_786053 : Nat := 4983230072969 + 3 ^ 40 * 786053 * 2
def baseEnd_786053 : Nat := 358776007918860709086679

theorem tailTrace_786053 : CollatzResearch.WordTrace tailWord_786053 prefixEnd_786053 358776007918860709086679 := by
  unfold tailWord_786053
  simp only [CollatzResearch.WordTrace]
  refine ⟨28669708221271703009546813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19113138814181135339697875 28669708221271703009546813)
  ·
    refine ⟨10751140582976888628580055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28669708221271703009546813 10751140582976888628580055)
    ·
      refine ⟨16126710874465332942870083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10751140582976888628580055 16126710874465332942870083)
      ·
        refine ⟨24190066311697999414305125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16126710874465332942870083 24190066311697999414305125)
        ·
          refine ⟨4535637433443374890182211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24190066311697999414305125 4535637433443374890182211)
          ·
            refine ⟨6803456150165062335273317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535637433443374890182211 6803456150165062335273317)
            ·
              refine ⟨1275648028155949187863747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6803456150165062335273317 1275648028155949187863747)
              ·
                refine ⟨1913472042233923781795621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275648028155949187863747 1913472042233923781795621)
                ·
                  refine ⟨358776007918860709086679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913472042233923781795621 358776007918860709086679)
                  ·
                    rfl

theorem cell20_786053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_786053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786053 prefixEnd_786053 := by exact prefixLift 786053
  have htrace : WordTrace (prefixWord ++ tailWord_786053) baseStart_786053 baseEnd_786053 := by
    simpa [prefixWord, tailWord_786053, baseEnd_786053] using wordTrace_append hprefix tailTrace_786053
  have hstable : (prefixWord ++ tailWord_786053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786053).length < 2 ^ (prefixWord ++ tailWord_786053).sum := by decide
  have hdescent : baseEnd_786053 < baseStart_786053 := by decide
  rcases family_descends (prefixWord ++ tailWord_786053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786094 : List Nat := [4, 1, 4, 1, 2, 2, 6]
def baseStart_786094 : Nat := 118140960795 + 786094 * 2 ^ 59
def prefixEnd_786094 : Nat := 4983230072969 + 3 ^ 40 * 786094 * 2
def baseEnd_786094 : Nat := 39866080159560754302205

theorem tailTrace_786094 : CollatzResearch.WordTrace tailWord_786094 prefixEnd_786094 39866080159560754302205 := by
  unfold tailWord_786094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583900451765395876473667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19114135742748778007859557 3583900451765395876473667)
  ·
    refine ⟨5375850677648093814710501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583900451765395876473667 5375850677648093814710501)
    ·
      refine ⟨1007972002059017590258219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5375850677648093814710501 1007972002059017590258219)
      ·
        refine ⟨1511958003088526385387329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007972002059017590258219 1511958003088526385387329)
        ·
          refine ⟨1133968502316394789040497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1511958003088526385387329 1133968502316394789040497)
          ·
            refine ⟨850476376737296091780373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1133968502316394789040497 850476376737296091780373)
            ·
              refine ⟨39866080159560754302205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 850476376737296091780373 39866080159560754302205)
              ·
                rfl

theorem cell20_786094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 6].length) (baseStart_786094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786094 prefixEnd_786094 := by exact prefixLift 786094
  have htrace : WordTrace (prefixWord ++ tailWord_786094) baseStart_786094 baseEnd_786094 := by
    simpa [prefixWord, tailWord_786094, baseEnd_786094] using wordTrace_append hprefix tailTrace_786094
  have hstable : (prefixWord ++ tailWord_786094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786094).length < 2 ^ (prefixWord ++ tailWord_786094).sum := by decide
  have hdescent : baseEnd_786094 < baseStart_786094 := by decide
  rcases family_descends (prefixWord ++ tailWord_786094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786105 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_786105 : Nat := 118140960795 + 786105 * 2 ^ 59
def prefixEnd_786105 : Nat := 4983230072969 + 3 ^ 40 * 786105 * 2
def baseEnd_786105 : Nat := 358799742135779639353133

theorem tailTrace_786105 : CollatzResearch.WordTrace tailWord_786105 prefixEnd_786105 358799742135779639353133 := by
  unfold tailWord_786105
  simp only [CollatzResearch.WordTrace]
  refine ⟨28671604817083315890439769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19114403211388877260293179 28671604817083315890439769)
  ·
    refine ⟨21503703612812486917829827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28671604817083315890439769 21503703612812486917829827)
    ·
      refine ⟨32255555419218730376744741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21503703612812486917829827 32255555419218730376744741)
      ·
        refine ⟨6047916641103511945639639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32255555419218730376744741 6047916641103511945639639)
        ·
          refine ⟨9071874961655267918459459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047916641103511945639639 9071874961655267918459459)
          ·
            refine ⟨13607812442482901877689189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9071874961655267918459459 13607812442482901877689189)
            ·
              refine ⟨2551464832965544102066723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13607812442482901877689189 2551464832965544102066723)
              ·
                refine ⟨3827197249448316153100085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551464832965544102066723 3827197249448316153100085)
                ·
                  refine ⟨358799742135779639353133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827197249448316153100085 358799742135779639353133)
                  ·
                    rfl

theorem cell20_786105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_786105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786105 prefixEnd_786105 := by exact prefixLift 786105
  have htrace : WordTrace (prefixWord ++ tailWord_786105) baseStart_786105 baseEnd_786105 := by
    simpa [prefixWord, tailWord_786105, baseEnd_786105] using wordTrace_append hprefix tailTrace_786105
  have hstable : (prefixWord ++ tailWord_786105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786105).length < 2 ^ (prefixWord ++ tailWord_786105).sum := by decide
  have hdescent : baseEnd_786105 < baseStart_786105 := by decide
  rcases family_descends (prefixWord ++ tailWord_786105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786108 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_786108 : Nat := 118140960795 + 786108 * 2 ^ 59
def prefixEnd_786108 : Nat := 4983230072969 + 3 ^ 40 * 786108 * 2
def baseEnd_786108 : Nat := 358801111417524962253121

theorem tailTrace_786108 : CollatzResearch.WordTrace tailWord_786108 prefixEnd_786108 358801111417524962253121 := by
  unfold tailWord_786108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14335857118036223701399489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19114476157381631601865985 14335857118036223701399489)
  ·
    refine ⟨10751892838527167776049617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14335857118036223701399489 10751892838527167776049617)
    ·
      refine ⟨8063919628895375832037213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10751892838527167776049617 8063919628895375832037213)
      ·
        refine ⟨3023969860835765937013955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8063919628895375832037213 3023969860835765937013955)
        ·
          refine ⟨4535954791253648905520933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023969860835765937013955 4535954791253648905520933)
          ·
            refine ⟨850491523360059169785175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4535954791253648905520933 850491523360059169785175)
            ·
              refine ⟨1275737285040088754677763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850491523360059169785175 1275737285040088754677763)
              ·
                refine ⟨1913605927560133132016645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275737285040088754677763 1913605927560133132016645)
                ·
                  refine ⟨358801111417524962253121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913605927560133132016645 358801111417524962253121)
                  ·
                    rfl

theorem cell20_786108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_786108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786108 prefixEnd_786108 := by exact prefixLift 786108
  have htrace : WordTrace (prefixWord ++ tailWord_786108) baseStart_786108 baseEnd_786108 := by
    simpa [prefixWord, tailWord_786108, baseEnd_786108] using wordTrace_append hprefix tailTrace_786108
  have hstable : (prefixWord ++ tailWord_786108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786108).length < 2 ^ (prefixWord ++ tailWord_786108).sum := by decide
  have hdescent : baseEnd_786108 < baseStart_786108 := by decide
  rcases family_descends (prefixWord ++ tailWord_786108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786188 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_786188 : Nat := 118140960795 + 786188 * 2 ^ 59
def prefixEnd_786188 : Nat := 4983230072969 + 3 ^ 40 * 786188 * 2
def baseEnd_786188 : Nat := 358837625597400239586127

theorem tailTrace_786188 : CollatzResearch.WordTrace tailWord_786188 prefixEnd_786188 358837625597400239586127 := by
  unfold tailWord_786188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337316037891310532855609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19116421383855080710474145 14337316037891310532855609)
  ·
    refine ⟨10752987028418482899641707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14337316037891310532855609 10752987028418482899641707)
    ·
      refine ⟨16129480542627724349462561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10752987028418482899641707 16129480542627724349462561)
      ·
        refine ⟨12097110406970793262096921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16129480542627724349462561 12097110406970793262096921)
        ·
          refine ⟨9072832805228094946572691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12097110406970793262096921 9072832805228094946572691)
          ·
            refine ⟨13609249207842142419859037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9072832805228094946572691 13609249207842142419859037)
            ·
              refine ⟨5103468452940803407447139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13609249207842142419859037 5103468452940803407447139)
              ·
                refine ⟨7655202679411205111170709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103468452940803407447139 7655202679411205111170709)
                ·
                  refine ⟨358837625597400239586127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7655202679411205111170709 358837625597400239586127)
                  ·
                    rfl

theorem cell20_786188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_786188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786188 prefixEnd_786188 := by exact prefixLift 786188
  have htrace : WordTrace (prefixWord ++ tailWord_786188) baseStart_786188 baseEnd_786188 := by
    simpa [prefixWord, tailWord_786188, baseEnd_786188] using wordTrace_append hprefix tailTrace_786188
  have hstable : (prefixWord ++ tailWord_786188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786188).length < 2 ^ (prefixWord ++ tailWord_786188).sum := by decide
  have hdescent : baseEnd_786188 < baseStart_786188 := by decide
  rcases family_descends (prefixWord ++ tailWord_786188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786212 : List Nat := [2, 3, 1, 3, 2, 2, 7]
def baseStart_786212 : Nat := 118140960795 + 786212 * 2 ^ 59
def prefixEnd_786212 : Nat := 4983230072969 + 3 ^ 40 * 786212 * 2
def baseEnd_786212 : Nat := 39872064427929202531781

theorem tailTrace_786212 : CollatzResearch.WordTrace tailWord_786212 prefixEnd_786212 39872064427929202531781 := by
  unfold tailWord_786212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337753713847836582292445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19117004951797115443056593 14337753713847836582292445)
  ·
    refine ⟨5376657642692938718359667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14337753713847836582292445 5376657642692938718359667)
    ·
      refine ⟨8064986464039408077539501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376657642692938718359667 8064986464039408077539501)
      ·
        refine ⟨3024369924014778029077313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8064986464039408077539501 3024369924014778029077313)
        ·
          refine ⟨2268277443011083521807985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024369924014778029077313 2268277443011083521807985)
          ·
            refine ⟨1701208082258312641355989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268277443011083521807985 1701208082258312641355989)
            ·
              refine ⟨39872064427929202531781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1701208082258312641355989 39872064427929202531781)
              ·
                rfl

theorem cell20_786212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_786212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786212 prefixEnd_786212 := by exact prefixLift 786212
  have htrace : WordTrace (prefixWord ++ tailWord_786212) baseStart_786212 baseEnd_786212 := by
    simpa [prefixWord, tailWord_786212, baseEnd_786212] using wordTrace_append hprefix tailTrace_786212
  have hstable : (prefixWord ++ tailWord_786212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786212).length < 2 ^ (prefixWord ++ tailWord_786212).sum := by decide
  have hdescent : baseEnd_786212 < baseStart_786212 := by decide
  rcases family_descends (prefixWord ++ tailWord_786212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786246 : List Nat := [6, 1, 1, 2, 1, 2, 1, 6]
def baseStart_786246 : Nat := 118140960795 + 786246 * 2 ^ 59
def prefixEnd_786246 : Nat := 4983230072969 + 3 ^ 40 * 786246 * 2
def baseEnd_786246 : Nat := 119621366125936605217519

theorem tailTrace_786246 : CollatzResearch.WordTrace tailWord_786246 prefixEnd_786246 119621366125936605217519 := by
  unfold tailWord_786246
  simp only [CollatzResearch.WordTrace]
  refine ⟨896148359674140530353831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19117831673048331314215061 896148359674140530353831)
  ·
    refine ⟨1344222539511210795530747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 896148359674140530353831 1344222539511210795530747)
    ·
      refine ⟨2016333809266816193296121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344222539511210795530747 2016333809266816193296121)
      ·
        refine ⟨1512250356950112144972091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2016333809266816193296121 1512250356950112144972091)
        ·
          refine ⟨2268375535425168217458137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512250356950112144972091 2268375535425168217458137)
          ·
            refine ⟨1701281651568876163093603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268375535425168217458137 1701281651568876163093603)
            ·
              refine ⟨2551922477353314244640405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701281651568876163093603 2551922477353314244640405)
              ·
                refine ⟨119621366125936605217519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2551922477353314244640405 119621366125936605217519)
                ·
                  rfl

theorem cell20_786246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_786246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786246 prefixEnd_786246 := by exact prefixLift 786246
  have htrace : WordTrace (prefixWord ++ tailWord_786246) baseStart_786246 baseEnd_786246 := by
    simpa [prefixWord, tailWord_786246, baseEnd_786246] using wordTrace_append hprefix tailTrace_786246
  have hstable : (prefixWord ++ tailWord_786246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786246).length < 2 ^ (prefixWord ++ tailWord_786246).sum := by decide
  have hdescent : baseEnd_786246 < baseStart_786246 := by decide
  rcases family_descends (prefixWord ++ tailWord_786246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786257 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_786257 : Nat := 118140960795 + 786257 * 2 ^ 59
def prefixEnd_786257 : Nat := 4983230072969 + 3 ^ 40 * 786257 * 2
def baseEnd_786257 : Nat := 358869119077542666285845

theorem tailTrace_786257 : CollatzResearch.WordTrace tailWord_786257 prefixEnd_786257 358869119077542666285845 := by
  unfold tailWord_786257
  simp only [CollatzResearch.WordTrace]
  refine ⟨28677148712532645849973025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19118099141688430566648683 28677148712532645849973025)
  ·
    refine ⟨21507861534399484387479769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28677148712532645849973025 21507861534399484387479769)
    ·
      refine ⟨16130896150799613290609827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21507861534399484387479769 16130896150799613290609827)
      ·
        refine ⟨24196344226199419935914741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16130896150799613290609827 24196344226199419935914741)
        ·
          refine ⟨2268407271206195618992007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24196344226199419935914741 2268407271206195618992007)
          ·
            refine ⟨3402610906809293428488011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268407271206195618992007 3402610906809293428488011)
            ·
              refine ⟨5103916360213940142732017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402610906809293428488011 5103916360213940142732017)
              ·
                refine ⟨3827937270160455107049013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5103916360213940142732017 3827937270160455107049013)
                ·
                  refine ⟨358869119077542666285845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827937270160455107049013 358869119077542666285845)
                  ·
                    rfl

theorem cell20_786257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_786257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786257 prefixEnd_786257 := by exact prefixLift 786257
  have htrace : WordTrace (prefixWord ++ tailWord_786257) baseStart_786257 baseEnd_786257 := by
    simpa [prefixWord, tailWord_786257, baseEnd_786257] using wordTrace_append hprefix tailTrace_786257
  have hstable : (prefixWord ++ tailWord_786257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786257).length < 2 ^ (prefixWord ++ tailWord_786257).sum := by decide
  have hdescent : baseEnd_786257 < baseStart_786257 := by decide
  rcases family_descends (prefixWord ++ tailWord_786257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786271 : List Nat := [1, 1, 2, 3, 1, 4, 8]
def baseStart_786271 : Nat := 118140960795 + 786271 * 2 ^ 59
def prefixEnd_786271 : Nat := 4983230072969 + 3 ^ 40 * 786271 * 2
def baseEnd_786271 : Nat := 39875056562113426646569

theorem tailTrace_786271 : CollatzResearch.WordTrace tailWord_786271 prefixEnd_786271 39875056562113426646569 := by
  unfold tailWord_786271
  simp only [CollatzResearch.WordTrace]
  refine ⟨28677659334481926240982667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19118439556321284160655111 28677659334481926240982667)
  ·
    refine ⟨43016489001722889361474001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28677659334481926240982667 43016489001722889361474001)
    ·
      refine ⟨32262366751292167021105501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43016489001722889361474001 32262366751292167021105501)
      ·
        refine ⟨12098387531734562632914563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32262366751292167021105501 12098387531734562632914563)
        ·
          refine ⟨18147581297601843949371845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12098387531734562632914563 18147581297601843949371845)
          ·
            refine ⟨3402671493300345740507221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18147581297601843949371845 3402671493300345740507221)
            ·
              refine ⟨39875056562113426646569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3402671493300345740507221 39875056562113426646569)
              ·
                rfl

theorem cell20_786271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_786271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786271 prefixEnd_786271 := by exact prefixLift 786271
  have htrace : WordTrace (prefixWord ++ tailWord_786271) baseStart_786271 baseEnd_786271 := by
    simpa [prefixWord, tailWord_786271, baseEnd_786271] using wordTrace_append hprefix tailTrace_786271
  have hstable : (prefixWord ++ tailWord_786271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786271).length < 2 ^ (prefixWord ++ tailWord_786271).sum := by decide
  have hdescent : baseEnd_786271 < baseStart_786271 := by decide
  rcases family_descends (prefixWord ++ tailWord_786271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786274 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_786274 : Nat := 118140960795 + 786274 * 2 ^ 59
def prefixEnd_786274 : Nat := 4983230072969 + 3 ^ 40 * 786274 * 2
def baseEnd_786274 : Nat := 358876878340766162719109

theorem tailTrace_786274 : CollatzResearch.WordTrace tailWord_786274 prefixEnd_786274 358876878340766162719109 := by
  unfold tailWord_786274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169442188367764438335469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19118512502314038502227917 7169442188367764438335469)
  ·
    refine ⟨2688540820637911664375801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7169442188367764438335469 2688540820637911664375801)
    ·
      refine ⟨2016405615478433748281851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2688540820637911664375801 2016405615478433748281851)
      ·
        refine ⟨3024608423217650622422777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016405615478433748281851 3024608423217650622422777)
        ·
          refine ⟨2268456317413237966817083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024608423217650622422777 2268456317413237966817083)
          ·
            refine ⟨3402684476119856950225625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268456317413237966817083 3402684476119856950225625)
            ·
              refine ⟨2552013357089892712669219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3402684476119856950225625 2552013357089892712669219)
              ·
                refine ⟨3828020035634839069003829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552013357089892712669219 3828020035634839069003829)
                ·
                  refine ⟨358876878340766162719109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3828020035634839069003829 358876878340766162719109)
                  ·
                    rfl

theorem cell20_786274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_786274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786274 prefixEnd_786274 := by exact prefixLift 786274
  have htrace : WordTrace (prefixWord ++ tailWord_786274) baseStart_786274 baseEnd_786274 := by
    simpa [prefixWord, tailWord_786274, baseEnd_786274] using wordTrace_append hprefix tailTrace_786274
  have hstable : (prefixWord ++ tailWord_786274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786274).length < 2 ^ (prefixWord ++ tailWord_786274).sum := by decide
  have hdescent : baseEnd_786274 < baseStart_786274 := by decide
  rcases family_descends (prefixWord ++ tailWord_786274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786281 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 2]
def baseStart_786281 : Nat := 118140960795 + 786281 * 2 ^ 59
def prefixEnd_786281 : Nat := 4983230072969 + 3 ^ 40 * 786281 * 2
def baseEnd_786281 : Nat := 358880073331505249485747

theorem tailTrace_786281 : CollatzResearch.WordTrace tailWord_786281 prefixEnd_786281 358880073331505249485747 := by
  unfold tailWord_786281
  simp only [CollatzResearch.WordTrace]
  refine ⟨28678024064445697948846697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19118682709630465299231131 28678024064445697948846697)
  ·
    refine ⟨21508518048334273461635023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28678024064445697948846697 21508518048334273461635023)
    ·
      refine ⟨32262777072501410192452535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21508518048334273461635023 32262777072501410192452535)
      ·
        refine ⟨48394165608752115288678803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32262777072501410192452535 48394165608752115288678803)
        ·
          refine ⟨72591248413128172933018205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48394165608752115288678803 72591248413128172933018205)
          ·
            refine ⟨27221718154923064849881827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72591248413128172933018205 27221718154923064849881827)
            ·
              refine ⟨40832577232384597274822741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27221718154923064849881827 40832577232384597274822741)
              ·
                refine ⟨478506764442006999314329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 40832577232384597274822741 478506764442006999314329)
                ·
                  refine ⟨358880073331505249485747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478506764442006999314329 358880073331505249485747)
                  ·
                    rfl

theorem cell20_786281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_786281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786281 prefixEnd_786281 := by exact prefixLift 786281
  have htrace : WordTrace (prefixWord ++ tailWord_786281) baseStart_786281 baseEnd_786281 := by
    simpa [prefixWord, tailWord_786281, baseEnd_786281] using wordTrace_append hprefix tailTrace_786281
  have hstable : (prefixWord ++ tailWord_786281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786281).length < 2 ^ (prefixWord ++ tailWord_786281).sum := by decide
  have hdescent : baseEnd_786281 < baseStart_786281 := by decide
  rcases family_descends (prefixWord ++ tailWord_786281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786309 : List Nat := [1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_786309 : Nat := 118140960795 + 786309 * 2 ^ 59
def prefixEnd_786309 : Nat := 4983230072969 + 3 ^ 40 * 786309 * 2
def baseEnd_786309 : Nat := 119630951098153865517433

theorem tailTrace_786309 : CollatzResearch.WordTrace tailWord_786309 prefixEnd_786309 119630951098153865517433 := by
  unfold tailWord_786309
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679045308344258730865981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19119363538896172487243987 28679045308344258730865981)
  ·
    refine ⟨10754641990629097024074743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28679045308344258730865981 10754641990629097024074743)
    ·
      refine ⟨16131962985943645536112115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10754641990629097024074743 16131962985943645536112115)
      ·
        refine ⟨24197944478915468304168173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16131962985943645536112115 24197944478915468304168173)
        ·
          refine ⟨9074229179593300614063065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24197944478915468304168173 9074229179593300614063065)
          ·
            refine ⟨6805671884694975460547299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9074229179593300614063065 6805671884694975460547299)
            ·
              refine ⟨10208507827042463190820949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6805671884694975460547299 10208507827042463190820949)
              ·
                refine ⟨119630951098153865517433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10208507827042463190820949 119630951098153865517433)
                ·
                  rfl

theorem cell20_786309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_786309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786309 prefixEnd_786309 := by exact prefixLift 786309
  have htrace : WordTrace (prefixWord ++ tailWord_786309) baseStart_786309 baseEnd_786309 := by
    simpa [prefixWord, tailWord_786309, baseEnd_786309] using wordTrace_append hprefix tailTrace_786309
  have hstable : (prefixWord ++ tailWord_786309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786309).length < 2 ^ (prefixWord ++ tailWord_786309).sum := by decide
  have hdescent : baseEnd_786309 < baseStart_786309 := by decide
  rcases family_descends (prefixWord ++ tailWord_786309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786332 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 2]
def baseStart_786332 : Nat := 118140960795 + 786332 * 2 ^ 59
def prefixEnd_786332 : Nat := 4983230072969 + 3 ^ 40 * 786332 * 2
def baseEnd_786332 : Nat := 358903351121175738785539

theorem tailTrace_786332 : CollatzResearch.WordTrace tailWord_786332 prefixEnd_786332 358903351121175738785539 := by
  unfold tailWord_786332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339942093630466829476625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19119922791507289105968833 14339942093630466829476625)
  ·
    refine ⟨10754956570222850122107469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14339942093630466829476625 10754956570222850122107469)
    ·
      refine ⟨4033108713833568795790301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10754956570222850122107469 4033108713833568795790301)
      ·
        refine ⟨1512415767687588298421363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4033108713833568795790301 1512415767687588298421363)
        ·
          refine ⟨2268623651531382447632045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512415767687588298421363 2268623651531382447632045)
          ·
            refine ⟨850733869324268417862017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2268623651531382447632045 850733869324268417862017)
            ·
              refine ⟨638050401993201313396513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850733869324268417862017 638050401993201313396513)
              ·
                refine ⟨478537801494900985047385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638050401993201313396513 478537801494900985047385)
                ·
                  refine ⟨358903351121175738785539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478537801494900985047385 358903351121175738785539)
                  ·
                    rfl

theorem cell20_786332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_786332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786332 prefixEnd_786332 := by exact prefixLift 786332
  have htrace : WordTrace (prefixWord ++ tailWord_786332) baseStart_786332 baseEnd_786332 := by
    simpa [prefixWord, tailWord_786332, baseEnd_786332] using wordTrace_append hprefix tailTrace_786332
  have hstable : (prefixWord ++ tailWord_786332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786332).length < 2 ^ (prefixWord ++ tailWord_786332).sum := by decide
  have hdescent : baseEnd_786332 < baseStart_786332 := by decide
  rcases family_descends (prefixWord ++ tailWord_786332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786343 : List Nat := [1, 1, 6, 1, 2, 3, 1, 5]
def baseStart_786343 : Nat := 118140960795 + 786343 * 2 ^ 59
def prefixEnd_786343 : Nat := 4983230072969 + 3 ^ 40 * 786343 * 2
def baseEnd_786343 : Nat := 119636123940302863139609

theorem tailTrace_786343 : CollatzResearch.WordTrace tailWord_786343 prefixEnd_786343 119636123940302863139609 := by
  unfold tailWord_786343
  simp only [CollatzResearch.WordTrace]
  refine ⟨28680285390221082537603683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19120190260147388358402455 28680285390221082537603683)
  ·
    refine ⟨43020428085331623806405525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28680285390221082537603683 43020428085331623806405525)
    ·
      refine ⟨2016582566499919865925259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43020428085331623806405525 2016582566499919865925259)
      ·
        refine ⟨3024873849749879798887889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016582566499919865925259 3024873849749879798887889)
        ·
          refine ⟨2268655387312409849165917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024873849749879798887889 2268655387312409849165917)
          ·
            refine ⟨850745770242153693437219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2268655387312409849165917 850745770242153693437219)
            ·
              refine ⟨1276118655363230540155829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850745770242153693437219 1276118655363230540155829)
              ·
                refine ⟨119636123940302863139609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1276118655363230540155829 119636123940302863139609)
                ·
                  rfl

theorem cell20_786343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_786343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786343 prefixEnd_786343 := by exact prefixLift 786343
  have htrace : WordTrace (prefixWord ++ tailWord_786343) baseStart_786343 baseEnd_786343 := by
    simpa [prefixWord, tailWord_786343, baseEnd_786343] using wordTrace_append hprefix tailTrace_786343
  have hstable : (prefixWord ++ tailWord_786343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786343).length < 2 ^ (prefixWord ++ tailWord_786343).sum := by decide
  have hdescent : baseEnd_786343 < baseStart_786343 := by decide
  rcases family_descends (prefixWord ++ tailWord_786343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786357 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_786357 : Nat := 118140960795 + 786357 * 2 ^ 59
def prefixEnd_786357 : Nat := 4983230072969 + 3 ^ 40 * 786357 * 2
def baseEnd_786357 : Nat := 358914761802386762952103

theorem tailTrace_786357 : CollatzResearch.WordTrace tailWord_786357 prefixEnd_786357 358914761802386762952103 := by
  unfold tailWord_786357
  simp only [CollatzResearch.WordTrace]
  refine ⟨28680796012170362928613325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19120530674780241952408883 28680796012170362928613325)
  ·
    refine ⟨10755298504563886098229997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28680796012170362928613325 10755298504563886098229997)
    ·
      refine ⟨4033236939211457286836249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10755298504563886098229997 4033236939211457286836249)
      ·
        refine ⟨3024927704408592965127187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4033236939211457286836249 3024927704408592965127187)
        ·
          refine ⟨4537391556612889447690781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024927704408592965127187 4537391556612889447690781)
          ·
            refine ⟨1701521833729833542884043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4537391556612889447690781 1701521833729833542884043)
            ·
              refine ⟨2552282750594750314326065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701521833729833542884043 2552282750594750314326065)
              ·
                refine ⟨1914212062946062735744549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552282750594750314326065 1914212062946062735744549)
                ·
                  refine ⟨358914761802386762952103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914212062946062735744549 358914761802386762952103)
                  ·
                    rfl

theorem cell20_786357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_786357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786357 prefixEnd_786357 := by exact prefixLift 786357
  have htrace : WordTrace (prefixWord ++ tailWord_786357) baseStart_786357 baseEnd_786357 := by
    simpa [prefixWord, tailWord_786357, baseEnd_786357] using wordTrace_append hprefix tailTrace_786357
  have hstable : (prefixWord ++ tailWord_786357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786357).length < 2 ^ (prefixWord ++ tailWord_786357).sum := by decide
  have hdescent : baseEnd_786357 < baseStart_786357 := by decide
  rcases family_descends (prefixWord ++ tailWord_786357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786416 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_786416 : Nat := 118140960795 + 786416 * 2 ^ 59
def prefixEnd_786416 : Nat := 4983230072969 + 3 ^ 40 * 786416 * 2
def baseEnd_786416 : Nat := 358941691010044779985195

theorem tailTrace_786416 : CollatzResearch.WordTrace tailWord_786416 prefixEnd_786416 358941691010044779985195 := by
  unfold tailWord_786416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14341473959478308002505551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19121965279304410670007401 14341473959478308002505551)
  ·
    refine ⟨21512210939217462003758327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14341473959478308002505551 21512210939217462003758327)
    ·
      refine ⟨32268316408826193005637491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21512210939217462003758327 32268316408826193005637491)
      ·
        refine ⟨48402474613239289508456237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32268316408826193005637491 48402474613239289508456237)
        ·
          refine ⟨18150927979964733565671089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48402474613239289508456237 18150927979964733565671089)
          ·
            refine ⟨13613195984973550174253317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18150927979964733565671089 13613195984973550174253317)
            ·
              refine ⟨2552474247182540657672497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13613195984973550174253317 2552474247182540657672497)
              ·
                refine ⟨1914355685386905493254373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552474247182540657672497 1914355685386905493254373)
                ·
                  refine ⟨358941691010044779985195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914355685386905493254373 358941691010044779985195)
                  ·
                    rfl

theorem cell20_786416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_786416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786416 prefixEnd_786416 := by exact prefixLift 786416
  have htrace : WordTrace (prefixWord ++ tailWord_786416) baseStart_786416 baseEnd_786416 := by
    simpa [prefixWord, tailWord_786416, baseEnd_786416] using wordTrace_append hprefix tailTrace_786416
  have hstable : (prefixWord ++ tailWord_786416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786416).length < 2 ^ (prefixWord ++ tailWord_786416).sum := by decide
  have hdescent : baseEnd_786416 < baseStart_786416 := by decide
  rcases family_descends (prefixWord ++ tailWord_786416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786436 : List Nat := [2, 3, 2, 4, 2, 1, 6]
def baseStart_786436 : Nat := 118140960795 + 786436 * 2 ^ 59
def prefixEnd_786436 : Nat := 4983230072969 + 3 ^ 40 * 786436 * 2
def baseEnd_786436 : Nat := 39883424395001511035383

theorem tailTrace_786436 : CollatzResearch.WordTrace tailWord_786436 prefixEnd_786436 39883424395001511035383 := by
  unfold tailWord_786436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14341838689442079710369581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19122451585922772947159441 14341838689442079710369581)
  ·
    refine ⟨5378189508540779891388593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14341838689442079710369581 5378189508540779891388593)
    ·
      refine ⟨4033642131405584918541445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5378189508540779891388593 4033642131405584918541445)
      ·
        refine ⟨756307899638547172226521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4033642131405584918541445 756307899638547172226521)
        ·
          refine ⟨567230924728910379169891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756307899638547172226521 567230924728910379169891)
          ·
            refine ⟨850846387093365568754837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567230924728910379169891 850846387093365568754837)
            ·
              refine ⟨39883424395001511035383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 850846387093365568754837 39883424395001511035383)
              ·
                rfl

theorem cell20_786436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 6].length) (baseStart_786436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786436 prefixEnd_786436 := by exact prefixLift 786436
  have htrace : WordTrace (prefixWord ++ tailWord_786436) baseStart_786436 baseEnd_786436 := by
    simpa [prefixWord, tailWord_786436, baseEnd_786436] using wordTrace_append hprefix tailTrace_786436
  have hstable : (prefixWord ++ tailWord_786436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786436).length < 2 ^ (prefixWord ++ tailWord_786436).sum := by decide
  have hdescent : baseEnd_786436 < baseStart_786436 := by decide
  rcases family_descends (prefixWord ++ tailWord_786436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786478 : List Nat := [4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_786478 : Nat := 118140960795 + 786478 * 2 ^ 59
def prefixEnd_786478 : Nat := 4983230072969 + 3 ^ 40 * 786478 * 2
def baseEnd_786478 : Nat := 119656663166482706639425

theorem tailTrace_786478 : CollatzResearch.WordTrace tailWord_786478 prefixEnd_786478 119656663166482706639425 := by
  unfold tailWord_786478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585651155591500074221011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19123472829821333729178725 3585651155591500074221011)
  ·
    refine ⟨5378476733387250111331517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3585651155591500074221011 5378476733387250111331517)
    ·
      refine ⟨2016928775020218791749319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5378476733387250111331517 2016928775020218791749319)
      ·
        refine ⟨3025393162530328187623979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016928775020218791749319 3025393162530328187623979)
        ·
          refine ⟨4538089743795492281435969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025393162530328187623979 4538089743795492281435969)
          ·
            refine ⟨3403567307846619211076977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4538089743795492281435969 3403567307846619211076977)
            ·
              refine ⟨2552675480884964408307733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3403567307846619211076977 2552675480884964408307733)
              ·
                refine ⟨119656663166482706639425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2552675480884964408307733 119656663166482706639425)
                ·
                  rfl

theorem cell20_786478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_786478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786478 prefixEnd_786478 := by exact prefixLift 786478
  have htrace : WordTrace (prefixWord ++ tailWord_786478) baseStart_786478 baseEnd_786478 := by
    simpa [prefixWord, tailWord_786478, baseEnd_786478] using wordTrace_append hprefix tailTrace_786478
  have hstable : (prefixWord ++ tailWord_786478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786478).length < 2 ^ (prefixWord ++ tailWord_786478).sum := by decide
  have hdescent : baseEnd_786478 < baseStart_786478 := by decide
  rcases family_descends (prefixWord ++ tailWord_786478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786509 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_786509 : Nat := 118140960795 + 786509 * 2 ^ 59
def prefixEnd_786509 : Nat := 4983230072969 + 3 ^ 40 * 786509 * 2
def baseEnd_786509 : Nat := 358984138744149789884815

theorem tailTrace_786509 : CollatzResearch.WordTrace tailWord_786509 prefixEnd_786509 358984138744149789884815 := by
  unfold tailWord_786509
  simp only [CollatzResearch.WordTrace]
  refine ⟨28686339907619692888146581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19124226605079795258764387 28686339907619692888146581)
  ·
    refine ⟨1344672183169673104131871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28686339907619692888146581 1344672183169673104131871)
    ·
      refine ⟨2017008274754509656197807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344672183169673104131871 2017008274754509656197807)
      ·
        refine ⟨3025512412131764484296711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017008274754509656197807 3025512412131764484296711)
        ·
          refine ⟨4538268618197646726445067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025512412131764484296711 4538268618197646726445067)
          ·
            refine ⟨6807402927296470089667601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538268618197646726445067 6807402927296470089667601)
            ·
              refine ⟨5105552195472352567250701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807402927296470089667601 5105552195472352567250701)
              ·
                refine ⟨1914582073302132212719013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5105552195472352567250701 1914582073302132212719013)
                ·
                  refine ⟨358984138744149789884815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914582073302132212719013 358984138744149789884815)
                  ·
                    rfl

theorem cell20_786509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_786509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786509 prefixEnd_786509 := by exact prefixLift 786509
  have htrace : WordTrace (prefixWord ++ tailWord_786509) baseStart_786509 baseEnd_786509 := by
    simpa [prefixWord, tailWord_786509, baseEnd_786509] using wordTrace_append hprefix tailTrace_786509
  have hstable : (prefixWord ++ tailWord_786509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786509).length < 2 ^ (prefixWord ++ tailWord_786509).sum := by decide
  have hdescent : baseEnd_786509 < baseStart_786509 := by decide
  rcases family_descends (prefixWord ++ tailWord_786509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786592 : List Nat := [2, 1, 1, 4, 2, 2, 4, 4]
def baseStart_786592 : Nat := 118140960795 + 786592 * 2 ^ 59
def prefixEnd_786592 : Nat := 4983230072969 + 3 ^ 40 * 786592 * 2
def baseEnd_786592 : Nat := 119674007401923463372603

theorem tailTrace_786592 : CollatzResearch.WordTrace tailWord_786592 prefixEnd_786592 119674007401923463372603 := by
  unfold tailWord_786592
  simp only [CollatzResearch.WordTrace]
  refine ⟨14344683583159499031709015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19126244777545998708945353 14344683583159499031709015)
  ·
    refine ⟨21517025374739248547563523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14344683583159499031709015 21517025374739248547563523)
    ·
      refine ⟨32275538062108872821345285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21517025374739248547563523 32275538062108872821345285)
      ·
        refine ⟨6051663386645413654002241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32275538062108872821345285 6051663386645413654002241)
        ·
          refine ⟨4538747539984060240501681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6051663386645413654002241 4538747539984060240501681)
          ·
            refine ⟨3404060654988045180376261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4538747539984060240501681 3404060654988045180376261)
            ·
              refine ⟨638261372810258471320549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3404060654988045180376261 638261372810258471320549)
              ·
                refine ⟨119674007401923463372603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 638261372810258471320549 119674007401923463372603)
                ·
                  rfl

theorem cell20_786592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_786592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786592 prefixEnd_786592 := by exact prefixLift 786592
  have htrace : WordTrace (prefixWord ++ tailWord_786592) baseStart_786592 baseEnd_786592 := by
    simpa [prefixWord, tailWord_786592, baseEnd_786592] using wordTrace_append hprefix tailTrace_786592
  have hstable : (prefixWord ++ tailWord_786592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786592).length < 2 ^ (prefixWord ++ tailWord_786592).sum := by decide
  have hdescent : baseEnd_786592 < baseStart_786592 := by decide
  rcases family_descends (prefixWord ++ tailWord_786592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786609 : List Nat := [1, 2, 2, 5, 3, 1, 6]
def baseStart_786609 : Nat := 118140960795 + 786609 * 2 ^ 59
def prefixEnd_786609 : Nat := 4983230072969 + 3 ^ 40 * 786609 * 2
def baseEnd_786609 : Nat := 39892197940999320727897

theorem tailTrace_786609 : CollatzResearch.WordTrace tailWord_786609 prefixEnd_786609 39892197940999320727897 := by
  unfold tailWord_786609
  simp only [CollatzResearch.WordTrace]
  refine ⟨28689987207257409966786881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19126658138171606644524587 28689987207257409966786881)
  ·
    refine ⟨21517490405443057475090161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28689987207257409966786881 21517490405443057475090161)
    ·
      refine ⟨16138117804082293106317621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21517490405443057475090161 16138117804082293106317621)
      ·
        refine ⟨1512948544132714978717277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16138117804082293106317621 1512948544132714978717277)
        ·
          refine ⟨567355704049768117018979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1512948544132714978717277 567355704049768117018979)
          ·
            refine ⟨851033556074652175528469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567355704049768117018979 851033556074652175528469)
            ·
              refine ⟨39892197940999320727897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 851033556074652175528469 39892197940999320727897)
              ·
                rfl

theorem cell20_786609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 6].length) (baseStart_786609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786609 prefixEnd_786609 := by exact prefixLift 786609
  have htrace : WordTrace (prefixWord ++ tailWord_786609) baseStart_786609 baseEnd_786609 := by
    simpa [prefixWord, tailWord_786609, baseEnd_786609] using wordTrace_append hprefix tailTrace_786609
  have hstable : (prefixWord ++ tailWord_786609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786609).length < 2 ^ (prefixWord ++ tailWord_786609).sum := by decide
  have hdescent : baseEnd_786609 < baseStart_786609 := by decide
  rcases family_descends (prefixWord ++ tailWord_786609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786626 : List Nat := [3, 5, 1, 1, 1, 2, 2, 5]
def baseStart_786626 : Nat := 118140960795 + 786626 * 2 ^ 59
def prefixEnd_786626 : Nat := 4983230072969 + 3 ^ 40 * 786626 * 2
def baseEnd_786626 : Nat := 119679180244072460994779

theorem tailTrace_786626 : CollatzResearch.WordTrace tailWord_786626 prefixEnd_786626 119679180244072460994779 := by
  unfold tailWord_786626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7172651812048955467538933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19127071498797214580103821 7172651812048955467538933)
  ·
    refine ⟨672436107379589575081775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7172651812048955467538933 672436107379589575081775)
    ·
      refine ⟨1008654161069384362622663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672436107379589575081775 1008654161069384362622663)
      ·
        refine ⟨1512981241604076543933995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008654161069384362622663 1512981241604076543933995)
        ·
          refine ⟨2269471862406114815900993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512981241604076543933995 2269471862406114815900993)
          ·
            refine ⟨1702103896804586111925745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2269471862406114815900993 1702103896804586111925745)
            ·
              refine ⟨1276577922603439583944309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702103896804586111925745 1276577922603439583944309)
              ·
                refine ⟨119679180244072460994779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1276577922603439583944309 119679180244072460994779)
                ·
                  rfl

theorem cell20_786626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_786626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786626 prefixEnd_786626 := by exact prefixLift 786626
  have htrace : WordTrace (prefixWord ++ tailWord_786626) baseStart_786626 baseEnd_786626 := by
    simpa [prefixWord, tailWord_786626, baseEnd_786626] using wordTrace_append hprefix tailTrace_786626
  have hstable : (prefixWord ++ tailWord_786626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786626).length < 2 ^ (prefixWord ++ tailWord_786626).sum := by decide
  have hdescent : baseEnd_786626 < baseStart_786626 := by decide
  rcases family_descends (prefixWord ++ tailWord_786626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786665 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_786665 : Nat := 118140960795 + 786665 * 2 ^ 59
def prefixEnd_786665 : Nat := 4983230072969 + 3 ^ 40 * 786665 * 2
def baseEnd_786665 : Nat := 359055341394906580684177

theorem tailTrace_786665 : CollatzResearch.WordTrace tailWord_786665 prefixEnd_786665 359055341394906580684177 := by
  unfold tailWord_786665
  simp only [CollatzResearch.WordTrace]
  refine ⟨28692029695054531530825449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19128019796703021020550299 28692029695054531530825449)
  ·
    refine ⟨21519022271290898648119087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28692029695054531530825449 21519022271290898648119087)
    ·
      refine ⟨32278533406936347972178631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21519022271290898648119087 32278533406936347972178631)
      ·
        refine ⟨48417800110404521958267947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32278533406936347972178631 48417800110404521958267947)
        ·
          refine ⟨72626700165606782937401921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48417800110404521958267947 72626700165606782937401921)
          ·
            refine ⟨54470025124205087203051441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72626700165606782937401921 54470025124205087203051441)
            ·
              refine ⟨40852518843153815402288581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54470025124205087203051441 40852518843153815402288581)
              ·
                refine ⟨7659847283091340387929109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40852518843153815402288581 7659847283091340387929109)
                ·
                  refine ⟨359055341394906580684177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7659847283091340387929109 359055341394906580684177)
                  ·
                    rfl

theorem cell20_786665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_786665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786665 prefixEnd_786665 := by exact prefixLift 786665
  have htrace : WordTrace (prefixWord ++ tailWord_786665) baseStart_786665 baseEnd_786665 := by
    simpa [prefixWord, tailWord_786665, baseEnd_786665] using wordTrace_append hprefix tailTrace_786665
  have hstable : (prefixWord ++ tailWord_786665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786665).length < 2 ^ (prefixWord ++ tailWord_786665).sum := by decide
  have hdescent : baseEnd_786665 < baseStart_786665 := by decide
  rcases family_descends (prefixWord ++ tailWord_786665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786675 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_786675 : Nat := 118140960795 + 786675 * 2 ^ 59
def prefixEnd_786675 : Nat := 4983230072969 + 3 ^ 40 * 786675 * 2
def baseEnd_786675 : Nat := 359059905667390990350803

theorem tailTrace_786675 : CollatzResearch.WordTrace tailWord_786675 prefixEnd_786675 359059905667390990350803 := by
  unfold tailWord_786675
  simp only [CollatzResearch.WordTrace]
  refine ⟨28692394425018303238689479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19128262950012202159126319 28692394425018303238689479)
  ·
    refine ⟨43038591637527454858034219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28692394425018303238689479 43038591637527454858034219)
    ·
      refine ⟨64557887456291182287051329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43038591637527454858034219 64557887456291182287051329)
      ·
        refine ⟨48418415592218386715288497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64557887456291182287051329 48418415592218386715288497)
        ·
          refine ⟨36313811694163790036466373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48418415592218386715288497 36313811694163790036466373)
          ·
            refine ⟨6808839692655710631837445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36313811694163790036466373 6808839692655710631837445)
            ·
              refine ⟨1276657442372945743469521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6808839692655710631837445 1276657442372945743469521)
              ·
                refine ⟨957493081779709307602141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276657442372945743469521 957493081779709307602141)
                ·
                  refine ⟨359059905667390990350803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957493081779709307602141 359059905667390990350803)
                  ·
                    rfl

theorem cell20_786675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_786675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786675 prefixEnd_786675 := by exact prefixLift 786675
  have htrace : WordTrace (prefixWord ++ tailWord_786675) baseStart_786675 baseEnd_786675 := by
    simpa [prefixWord, tailWord_786675, baseEnd_786675] using wordTrace_append hprefix tailTrace_786675
  have hstable : (prefixWord ++ tailWord_786675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786675).length < 2 ^ (prefixWord ++ tailWord_786675).sum := by decide
  have hdescent : baseEnd_786675 < baseStart_786675 := by decide
  rcases family_descends (prefixWord ++ tailWord_786675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786730 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_786730 : Nat := 118140960795 + 786730 * 2 ^ 59
def prefixEnd_786730 : Nat := 4983230072969 + 3 ^ 40 * 786730 * 2
def baseEnd_786730 : Nat := 359085009166055243517245

theorem tailTrace_786730 : CollatzResearch.WordTrace tailWord_786730 prefixEnd_786730 359085009166055243517245 := by
  unfold tailWord_786730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173600109954761907985411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19129600293212698421294429 7173600109954761907985411)
  ·
    refine ⟨10760400164932142861978117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7173600109954761907985411 10760400164932142861978117)
    ·
      refine ⟨2017575030924776786620897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10760400164932142861978117 2017575030924776786620897)
      ·
        refine ⟨1513181273193582589965673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2017575030924776786620897 1513181273193582589965673)
        ·
          refine ⟨1134885954895186942474255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513181273193582589965673 1134885954895186942474255)
          ·
            refine ⟨1702328932342780413711383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134885954895186942474255 1702328932342780413711383)
            ·
              refine ⟨2553493398514170620567075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702328932342780413711383 2553493398514170620567075)
              ·
                refine ⟨3830240097771255930850613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553493398514170620567075 3830240097771255930850613)
                ·
                  refine ⟨359085009166055243517245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3830240097771255930850613 359085009166055243517245)
                  ·
                    rfl

theorem cell20_786730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_786730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786730 prefixEnd_786730 := by exact prefixLift 786730
  have htrace : WordTrace (prefixWord ++ tailWord_786730) baseStart_786730 baseEnd_786730 := by
    simpa [prefixWord, tailWord_786730, baseEnd_786730] using wordTrace_append hprefix tailTrace_786730
  have hstable : (prefixWord ++ tailWord_786730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786730).length < 2 ^ (prefixWord ++ tailWord_786730).sum := by decide
  have hdescent : baseEnd_786730 < baseStart_786730 := by decide
  rcases family_descends (prefixWord ++ tailWord_786730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786737 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_786737 : Nat := 118140960795 + 786737 * 2 ^ 59
def prefixEnd_786737 : Nat := 4983230072969 + 3 ^ 40 * 786737 * 2
def baseEnd_786737 : Nat := 359088204156794330283883

theorem tailTrace_786737 : CollatzResearch.WordTrace tailWord_786737 prefixEnd_786737 359088204156794330283883 := by
  unfold tailWord_786737
  simp only [CollatzResearch.WordTrace]
  refine ⟨28694655750793687827446465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19129770500529125218297643 28694655750793687827446465)
  ·
    refine ⟨21520991813095265870584849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28694655750793687827446465 21520991813095265870584849)
    ·
      refine ⟨16140743859821449402938637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21520991813095265870584849 16140743859821449402938637)
      ·
        refine ⟨6052778947433043526101989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16140743859821449402938637 6052778947433043526101989)
        ·
          refine ⟨1134896052643695661144123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6052778947433043526101989 1134896052643695661144123)
          ·
            refine ⟨1702344078965543491716185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134896052643695661144123 1702344078965543491716185)
            ·
              refine ⟨1276758059224157618787139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702344078965543491716185 1276758059224157618787139)
              ·
                refine ⟨1915137088836236428180709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276758059224157618787139 1915137088836236428180709)
                ·
                  refine ⟨359088204156794330283883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915137088836236428180709 359088204156794330283883)
                  ·
                    rfl

theorem cell20_786737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_786737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786737 prefixEnd_786737 := by exact prefixLift 786737
  have htrace : WordTrace (prefixWord ++ tailWord_786737) baseStart_786737 baseEnd_786737 := by
    simpa [prefixWord, tailWord_786737, baseEnd_786737] using wordTrace_append hprefix tailTrace_786737
  have hstable : (prefixWord ++ tailWord_786737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786737).length < 2 ^ (prefixWord ++ tailWord_786737).sum := by decide
  have hdescent : baseEnd_786737 < baseStart_786737 := by decide
  rcases family_descends (prefixWord ++ tailWord_786737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786851 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 2]
def baseStart_786851 : Nat := 118140960795 + 786851 * 2 ^ 59
def prefixEnd_786851 : Nat := 4983230072969 + 3 ^ 40 * 786851 * 2
def baseEnd_786851 : Nat := 359140236863116600483417

theorem tailTrace_786851 : CollatzResearch.WordTrace tailWord_786851 prefixEnd_786851 359140236863116600483417 := by
  unfold tailWord_786851
  simp only [CollatzResearch.WordTrace]
  refine ⟨28698813672380685297096407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19132542448253790198064271 28698813672380685297096407)
  ·
    refine ⟨43048220508571027945644611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28698813672380685297096407 43048220508571027945644611)
    ·
      refine ⟨64572330762856541918466917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43048220508571027945644611 64572330762856541918466917)
      ·
        refine ⟨12107312018035601609712547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64572330762856541918466917 12107312018035601609712547)
        ·
          refine ⟨18160968027053402414568821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12107312018035601609712547 18160968027053402414568821)
          ·
            refine ⟨1702590752536256476365827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18160968027053402414568821 1702590752536256476365827)
            ·
              refine ⟨2553886128804384714548741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702590752536256476365827 2553886128804384714548741)
              ·
                refine ⟨478853649150822133977889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2553886128804384714548741 478853649150822133977889)
                ·
                  refine ⟨359140236863116600483417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478853649150822133977889 359140236863116600483417)
                  ·
                    rfl

theorem cell20_786851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 2].length) (baseStart_786851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786851 prefixEnd_786851 := by exact prefixLift 786851
  have htrace : WordTrace (prefixWord ++ tailWord_786851) baseStart_786851 baseEnd_786851 := by
    simpa [prefixWord, tailWord_786851, baseEnd_786851] using wordTrace_append hprefix tailTrace_786851
  have hstable : (prefixWord ++ tailWord_786851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786851).length < 2 ^ (prefixWord ++ tailWord_786851).sum := by decide
  have hdescent : baseEnd_786851 < baseStart_786851 := by decide
  rcases family_descends (prefixWord ++ tailWord_786851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786865 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_786865 : Nat := 118140960795 + 786865 * 2 ^ 59
def prefixEnd_786865 : Nat := 4983230072969 + 3 ^ 40 * 786865 * 2
def baseEnd_786865 : Nat := 359146626844594774016693

theorem tailTrace_786865 : CollatzResearch.WordTrace tailWord_786865 prefixEnd_786865 359146626844594774016693 := by
  unfold tailWord_786865
  simp only [CollatzResearch.WordTrace]
  refine ⟨28699324294329965688106049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19132882862886643792070699 28699324294329965688106049)
  ·
    refine ⟨21524493220747474266079537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28699324294329965688106049 21524493220747474266079537)
    ·
      refine ⟨16143369915560605699559653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21524493220747474266079537 16143369915560605699559653)
      ·
        refine ⟨3026881859167613568667435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16143369915560605699559653 3026881859167613568667435)
        ·
          refine ⟨4540322788751420353001153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026881859167613568667435 4540322788751420353001153)
          ·
            refine ⟨3405242091563565264750865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4540322788751420353001153 3405242091563565264750865)
            ·
              refine ⟨2553931568672673948563149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3405242091563565264750865 2553931568672673948563149)
              ·
                refine ⟨957724338252252730711181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2553931568672673948563149 957724338252252730711181)
                ·
                  refine ⟨359146626844594774016693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957724338252252730711181 359146626844594774016693)
                  ·
                    rfl

theorem cell20_786865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_786865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786865 prefixEnd_786865 := by exact prefixLift 786865
  have htrace : WordTrace (prefixWord ++ tailWord_786865) baseStart_786865 baseEnd_786865 := by
    simpa [prefixWord, tailWord_786865, baseEnd_786865] using wordTrace_append hprefix tailTrace_786865
  have hstable : (prefixWord ++ tailWord_786865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786865).length < 2 ^ (prefixWord ++ tailWord_786865).sum := by decide
  have hdescent : baseEnd_786865 < baseStart_786865 := by decide
  rcases family_descends (prefixWord ++ tailWord_786865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786920 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_786920 : Nat := 118140960795 + 786920 * 2 ^ 59
def prefixEnd_786920 : Nat := 4983230072969 + 3 ^ 40 * 786920 * 2
def baseEnd_786920 : Nat := 359171730343259027183135

theorem tailTrace_786920 : CollatzResearch.WordTrace tailWord_786920 prefixEnd_786920 359171730343259027183135 := by
  unfold tailWord_786920
  simp only [CollatzResearch.WordTrace]
  refine ⟨14350665154565355040679107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19134220206087140054238809 14350665154565355040679107)
  ·
    refine ⟨21525997731848032561018661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14350665154565355040679107 21525997731848032561018661)
    ·
      refine ⟨4036124574721506105190999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21525997731848032561018661 4036124574721506105190999)
      ·
        refine ⟨6054186862082259157786499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036124574721506105190999 6054186862082259157786499)
        ·
          refine ⟨9081280293123388736679749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054186862082259157786499 9081280293123388736679749)
          ·
            refine ⟨1702740054960635388127453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9081280293123388736679749 1702740054960635388127453)
            ·
              refine ⟨638527520610238270547795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1702740054960635388127453 638527520610238270547795)
              ·
                refine ⟨957791280915357405821693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638527520610238270547795 957791280915357405821693)
                ·
                  refine ⟨359171730343259027183135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957791280915357405821693 359171730343259027183135)
                  ·
                    rfl

theorem cell20_786920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_786920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786920 prefixEnd_786920 := by exact prefixLift 786920
  have htrace : WordTrace (prefixWord ++ tailWord_786920) baseStart_786920 baseEnd_786920 := by
    simpa [prefixWord, tailWord_786920, baseEnd_786920] using wordTrace_append hprefix tailTrace_786920
  have hstable : (prefixWord ++ tailWord_786920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786920).length < 2 ^ (prefixWord ++ tailWord_786920).sum := by decide
  have hdescent : baseEnd_786920 < baseStart_786920 := by decide
  rcases family_descends (prefixWord ++ tailWord_786920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786930 : List Nat := [3, 2, 1, 4, 3, 1, 2, 4]
def baseStart_786930 : Nat := 118140960795 + 786930 * 2 ^ 59
def prefixEnd_786930 : Nat := 4983230072969 + 3 ^ 40 * 786930 * 2
def baseEnd_786930 : Nat := 119725431538581145616587

theorem tailTrace_786930 : CollatzResearch.WordTrace tailWord_786930 prefixEnd_786930 119725431538581145616587 := by
  unfold tailWord_786930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175423759773620447305561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19134463359396321192814829 7175423759773620447305561)
  ·
    refine ⟨5381567819830215335479171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7175423759773620447305561 5381567819830215335479171)
    ·
      refine ⟨8072351729745323003218757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381567819830215335479171 8072351729745323003218757)
      ·
        refine ⟨1513565949327248063103517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8072351729745323003218757 1513565949327248063103517)
        ·
          refine ⟨567587230997718023663819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1513565949327248063103517 567587230997718023663819)
          ·
            refine ⟨851380846496577035495729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567587230997718023663819 851380846496577035495729)
            ·
              refine ⟨638535634872432776621797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851380846496577035495729 638535634872432776621797)
              ·
                refine ⟨119725431538581145616587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 638535634872432776621797 119725431538581145616587)
                ·
                  rfl

theorem cell20_786930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_786930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786930 prefixEnd_786930 := by exact prefixLift 786930
  have htrace : WordTrace (prefixWord ++ tailWord_786930) baseStart_786930 baseEnd_786930 := by
    simpa [prefixWord, tailWord_786930, baseEnd_786930] using wordTrace_append hprefix tailTrace_786930
  have hstable : (prefixWord ++ tailWord_786930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786930).length < 2 ^ (prefixWord ++ tailWord_786930).sum := by decide
  have hdescent : baseEnd_786930 < baseStart_786930 := by decide
  rcases family_descends (prefixWord ++ tailWord_786930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786931 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_786931 : Nat := 118140960795 + 786931 * 2 ^ 59
def prefixEnd_786931 : Nat := 4983230072969 + 3 ^ 40 * 786931 * 2
def baseEnd_786931 : Nat := 359176751042991877816423

theorem tailTrace_786931 : CollatzResearch.WordTrace tailWord_786931 prefixEnd_786931 359176751042991877816423 := by
  unfold tailWord_786931
  simp only [CollatzResearch.WordTrace]
  refine ⟨28701731512090858960008647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19134487674727239306672431 28701731512090858960008647)
  ·
    refine ⟨43052597268136288440012971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28701731512090858960008647 43052597268136288440012971)
    ·
      refine ⟨64578895902204432660019457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43052597268136288440012971 64578895902204432660019457)
      ·
        refine ⟨48434171926653324495014593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64578895902204432660019457 48434171926653324495014593)
        ·
          refine ⟨36325628944989993371260945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48434171926653324495014593 36325628944989993371260945)
          ·
            refine ⟨27244221708742495028445709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36325628944989993371260945 27244221708742495028445709)
            ·
              refine ⟨10216583140778435635667141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27244221708742495028445709 10216583140778435635667141)
              ·
                refine ⟨1915609338895956681687589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10216583140778435635667141 1915609338895956681687589)
                ·
                  refine ⟨359176751042991877816423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915609338895956681687589 359176751042991877816423)
                  ·
                    rfl

theorem cell20_786931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_786931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786931 prefixEnd_786931 := by exact prefixLift 786931
  have htrace : WordTrace (prefixWord ++ tailWord_786931) baseStart_786931 baseEnd_786931 := by
    simpa [prefixWord, tailWord_786931, baseEnd_786931] using wordTrace_append hprefix tailTrace_786931
  have hstable : (prefixWord ++ tailWord_786931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786931).length < 2 ^ (prefixWord ++ tailWord_786931).sum := by decide
  have hdescent : baseEnd_786931 < baseStart_786931 := by decide
  rcases family_descends (prefixWord ++ tailWord_786931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786955 : List Nat := [1, 1, 1, 1, 7, 3, 6]
def baseStart_786955 : Nat := 118140960795 + 786955 * 2 ^ 59
def prefixEnd_786955 : Nat := 4983230072969 + 3 ^ 40 * 786955 * 2
def baseEnd_786955 : Nat := 39909745032994940112925

theorem tailTrace_786955 : CollatzResearch.WordTrace tailWord_786955 prefixEnd_786955 39909745032994940112925 := by
  unfold tailWord_786955
  simp only [CollatzResearch.WordTrace]
  refine ⟨28702606864003911058882319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19135071242669274039254879 28702606864003911058882319)
  ·
    refine ⟨43053910296005866588323479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28702606864003911058882319 43053910296005866588323479)
    ·
      refine ⟨64580865444008799882485219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43053910296005866588323479 64580865444008799882485219)
      ·
        refine ⟨96871298166013199823727829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64580865444008799882485219 96871298166013199823727829)
        ·
          refine ⟨2270421050765934370868621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 96871298166013199823727829 2270421050765934370868621)
          ·
            refine ⟨851407894037225389075733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2270421050765934370868621 851407894037225389075733)
            ·
              refine ⟨39909745032994940112925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 851407894037225389075733 39909745032994940112925)
              ·
                rfl

theorem cell20_786955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_786955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786955 prefixEnd_786955 := by exact prefixLift 786955
  have htrace : WordTrace (prefixWord ++ tailWord_786955) baseStart_786955 baseEnd_786955 := by
    simpa [prefixWord, tailWord_786955, baseEnd_786955] using wordTrace_append hprefix tailTrace_786955
  have hstable : (prefixWord ++ tailWord_786955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786955).length < 2 ^ (prefixWord ++ tailWord_786955).sum := by decide
  have hdescent : baseEnd_786955 < baseStart_786955 := by decide
  rcases family_descends (prefixWord ++ tailWord_786955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786979 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_786979 : Nat := 118140960795 + 786979 * 2 ^ 59
def prefixEnd_786979 : Nat := 4983230072969 + 3 ^ 40 * 786979 * 2
def baseEnd_786979 : Nat := 359198659550917044216227

theorem tailTrace_786979 : CollatzResearch.WordTrace tailWord_786979 prefixEnd_786979 359198659550917044216227 := by
  unfold tailWord_786979
  simp only [CollatzResearch.WordTrace]
  refine ⟨28703482215916963157755991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19135654810611308771837327 28703482215916963157755991)
  ·
    refine ⟨43055223323875444736633987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28703482215916963157755991 43055223323875444736633987)
    ·
      refine ⟨64582834985813167104950981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43055223323875444736633987 64582834985813167104950981)
      ·
        refine ⟨12109281559839968832178309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64582834985813167104950981 12109281559839968832178309)
        ·
          refine ⟨2270490292469994156033433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12109281559839968832178309 2270490292469994156033433)
          ·
            refine ⟨1702867719352495617025075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2270490292469994156033433 1702867719352495617025075)
            ·
              refine ⟨2554301579028743425537613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702867719352495617025075 2554301579028743425537613)
              ·
                refine ⟨957863092135778784576605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2554301579028743425537613 957863092135778784576605)
                ·
                  refine ⟨359198659550917044216227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957863092135778784576605 359198659550917044216227)
                  ·
                    rfl

theorem cell20_786979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_786979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_786979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_786979 prefixEnd_786979 := by exact prefixLift 786979
  have htrace : WordTrace (prefixWord ++ tailWord_786979) baseStart_786979 baseEnd_786979 := by
    simpa [prefixWord, tailWord_786979, baseEnd_786979] using wordTrace_append hprefix tailTrace_786979
  have hstable : (prefixWord ++ tailWord_786979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786979).length < 2 ^ (prefixWord ++ tailWord_786979).sum := by decide
  have hdescent : baseEnd_786979 < baseStart_786979 := by decide
  rcases family_descends (prefixWord ++ tailWord_786979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787012 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 2]
def baseStart_787012 : Nat := 118140960795 + 787012 * 2 ^ 59
def prefixEnd_787012 : Nat := 4983230072969 + 3 ^ 40 * 787012 * 2
def baseEnd_787012 : Nat := 359213721650115596116093

theorem tailTrace_787012 : CollatzResearch.WordTrace tailWord_787012 prefixEnd_787012 359213721650115596116093 := by
  unfold tailWord_787012
  simp only [CollatzResearch.WordTrace]
  refine ⟨14352342912398704896853645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19136457216531606529138193 14352342912398704896853645)
  ·
    refine ⟨5382128592149514336320117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14352342912398704896853645 5382128592149514336320117)
    ·
      refine ⟨504574555514016969030011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5382128592149514336320117 504574555514016969030011)
      ·
        refine ⟨756861833271025453545017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504574555514016969030011 756861833271025453545017)
        ·
          refine ⟨567646374953269090158763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756861833271025453545017 567646374953269090158763)
          ·
            refine ⟨851469562429903635238145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567646374953269090158763 851469562429903635238145)
            ·
              refine ⟨638602171822427726428609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851469562429903635238145 638602171822427726428609)
              ·
                refine ⟨478951628866820794821457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638602171822427726428609 478951628866820794821457)
                ·
                  refine ⟨359213721650115596116093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478951628866820794821457 359213721650115596116093)
                  ·
                    rfl

theorem cell20_787012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_787012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787012 prefixEnd_787012 := by exact prefixLift 787012
  have htrace : WordTrace (prefixWord ++ tailWord_787012) baseStart_787012 baseEnd_787012 := by
    simpa [prefixWord, tailWord_787012, baseEnd_787012] using wordTrace_append hprefix tailTrace_787012
  have hstable : (prefixWord ++ tailWord_787012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787012).length < 2 ^ (prefixWord ++ tailWord_787012).sum := by decide
  have hdescent : baseEnd_787012 < baseStart_787012 := by decide
  rcases family_descends (prefixWord ++ tailWord_787012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787052 : List Nat := [2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_787052 : Nat := 118140960795 + 787052 * 2 ^ 59
def prefixEnd_787052 : Nat := 4983230072969 + 3 ^ 40 * 787052 * 2
def baseEnd_787052 : Nat := 119743992913351078260865

theorem tailTrace_787052 : CollatzResearch.WordTrace tailWord_787052 prefixEnd_787052 119743992913351078260865 := by
  unfold tailWord_787052
  simp only [CollatzResearch.WordTrace]
  refine ⟨14353072372326248312581705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19137429829768331083442273 14353072372326248312581705)
  ·
    refine ⟨10764804279244686234436279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14353072372326248312581705 10764804279244686234436279)
    ·
      refine ⟨16147206418867029351654419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10764804279244686234436279 16147206418867029351654419)
      ·
        refine ⟨24220809628300544027481629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16147206418867029351654419 24220809628300544027481629)
        ·
          refine ⟨9082803610612704010305611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24220809628300544027481629 9082803610612704010305611)
          ·
            refine ⟨13624205415919056015458417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9082803610612704010305611 13624205415919056015458417)
            ·
              refine ⟨10218154061939292011593813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13624205415919056015458417 10218154061939292011593813)
              ·
                refine ⟨119743992913351078260865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10218154061939292011593813 119743992913351078260865)
                ·
                  rfl

theorem cell20_787052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_787052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787052 prefixEnd_787052 := by exact prefixLift 787052
  have htrace : WordTrace (prefixWord ++ tailWord_787052) baseStart_787052 baseEnd_787052 := by
    simpa [prefixWord, tailWord_787052, baseEnd_787052] using wordTrace_append hprefix tailTrace_787052
  have hstable : (prefixWord ++ tailWord_787052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787052).length < 2 ^ (prefixWord ++ tailWord_787052).sum := by decide
  have hdescent : baseEnd_787052 < baseStart_787052 := by decide
  rcases family_descends (prefixWord ++ tailWord_787052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787058 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_787058 : Nat := 118140960795 + 787058 * 2 ^ 59
def prefixEnd_787058 : Nat := 4983230072969 + 3 ^ 40 * 787058 * 2
def baseEnd_787058 : Nat := 359234717303543880582571

theorem tailTrace_787058 : CollatzResearch.WordTrace tailWord_787058 prefixEnd_787058 359234717303543880582571 := by
  unfold tailWord_787058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176590895657689912470457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19137575721753839766587885 7176590895657689912470457)
  ·
    refine ⟨5382443171743267434352843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7176590895657689912470457 5382443171743267434352843)
    ·
      refine ⟨8073664757614901151529265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5382443171743267434352843 8073664757614901151529265)
      ·
        refine ⟨6055248568211175863646949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8073664757614901151529265 6055248568211175863646949)
        ·
          refine ⟨1135359106539595474433803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6055248568211175863646949 1135359106539595474433803)
          ·
            refine ⟨1703038659809393211650705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135359106539595474433803 1703038659809393211650705)
            ·
              refine ⟨1277278994857044908738029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703038659809393211650705 1277278994857044908738029)
              ·
                refine ⟨478979623071391840776761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1277278994857044908738029 478979623071391840776761)
                ·
                  refine ⟨359234717303543880582571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478979623071391840776761 359234717303543880582571)
                  ·
                    rfl

theorem cell20_787058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_787058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787058 prefixEnd_787058 := by exact prefixLift 787058
  have htrace : WordTrace (prefixWord ++ tailWord_787058) baseStart_787058 baseEnd_787058 := by
    simpa [prefixWord, tailWord_787058, baseEnd_787058] using wordTrace_append hprefix tailTrace_787058
  have hstable : (prefixWord ++ tailWord_787058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787058).length < 2 ^ (prefixWord ++ tailWord_787058).sum := by decide
  have hdescent : baseEnd_787058 < baseStart_787058 := by decide
  rcases family_descends (prefixWord ++ tailWord_787058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787069 : List Nat := [1, 4, 1, 1, 5, 1, 7]
def baseStart_787069 : Nat := 118140960795 + 787069 * 2 ^ 59
def prefixEnd_787069 : Nat := 4983230072969 + 3 ^ 40 * 787069 * 2
def baseEnd_787069 : Nat := 39915526444808525690651

theorem tailTrace_787069 : CollatzResearch.WordTrace tailWord_787069 prefixEnd_787069 39915526444808525690651 := by
  unfold tailWord_787069
  simp only [CollatzResearch.WordTrace]
  refine ⟨28706764785590908528532261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19137843190393939019021507 28706764785590908528532261)
  ·
    refine ⟨5382518397298295349099799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28706764785590908528532261 5382518397298295349099799)
    ·
      refine ⟨8073777595947443023649699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5382518397298295349099799 8073777595947443023649699)
      ·
        refine ⟨12110666393921164535474549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8073777595947443023649699 12110666393921164535474549)
        ·
          refine ⟨1135374974430109175200739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12110666393921164535474549 1135374974430109175200739)
          ·
            refine ⟨1703062461645163762801109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135374974430109175200739 1703062461645163762801109)
            ·
              refine ⟨39915526444808525690651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1703062461645163762801109 39915526444808525690651)
              ·
                rfl

theorem cell20_787069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_787069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787069 prefixEnd_787069 := by exact prefixLift 787069
  have htrace : WordTrace (prefixWord ++ tailWord_787069) baseStart_787069 baseEnd_787069 := by
    simpa [prefixWord, tailWord_787069, baseEnd_787069] using wordTrace_append hprefix tailTrace_787069
  have hstable : (prefixWord ++ tailWord_787069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787069).length < 2 ^ (prefixWord ++ tailWord_787069).sum := by decide
  have hdescent : baseEnd_787069 < baseStart_787069 := by decide
  rcases family_descends (prefixWord ++ tailWord_787069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787100 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_787100 : Nat := 118140960795 + 787100 * 2 ^ 59
def prefixEnd_787100 : Nat := 4983230072969 + 3 ^ 40 * 787100 * 2
def baseEnd_787100 : Nat := 359253887247978401182399

theorem tailTrace_787100 : CollatzResearch.WordTrace tailWord_787100 prefixEnd_787100 359253887247978401182399 := by
  unfold tailWord_787100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14353947724239300411455377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19138596965652400548607169 14353947724239300411455377)
  ·
    refine ⟨10765460793179475308591533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14353947724239300411455377 10765460793179475308591533)
    ·
      refine ⟨4037047797442303240721825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10765460793179475308591533 4037047797442303240721825)
      ·
        refine ⟨3027785848081727430541369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4037047797442303240721825 3027785848081727430541369)
        ·
          refine ⟨2270839386061295572906027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3027785848081727430541369 2270839386061295572906027)
          ·
            refine ⟨3406259079091943359359041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270839386061295572906027 3406259079091943359359041)
            ·
              refine ⟨2554694309318957519519281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406259079091943359359041 2554694309318957519519281)
              ·
                refine ⟨1916020731989218139639461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554694309318957519519281 1916020731989218139639461)
                ·
                  refine ⟨359253887247978401182399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916020731989218139639461 359253887247978401182399)
                  ·
                    rfl

theorem cell20_787100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_787100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787100 prefixEnd_787100 := by exact prefixLift 787100
  have htrace : WordTrace (prefixWord ++ tailWord_787100) baseStart_787100 baseEnd_787100 := by
    simpa [prefixWord, tailWord_787100, baseEnd_787100] using wordTrace_append hprefix tailTrace_787100
  have hstable : (prefixWord ++ tailWord_787100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787100).length < 2 ^ (prefixWord ++ tailWord_787100).sum := by decide
  have hdescent : baseEnd_787100 < baseStart_787100 := by decide
  rcases family_descends (prefixWord ++ tailWord_787100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787134 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_787134 : Nat := 118140960795 + 787134 * 2 ^ 59
def prefixEnd_787134 : Nat := 4983230072969 + 3 ^ 40 * 787134 * 2
def baseEnd_787134 : Nat := 359269405774425394048927

theorem tailTrace_787134 : CollatzResearch.WordTrace tailWord_787134 prefixEnd_787134 359269405774425394048927 := by
  unfold tailWord_787134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3588641941294428078706057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19139423686903616419765637 3588641941294428078706057)
  ·
    refine ⟨2691481455970821059029543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3588641941294428078706057 2691481455970821059029543)
    ·
      refine ⟨4037222183956231588544315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691481455970821059029543 4037222183956231588544315)
      ·
        refine ⟨6055833275934347382816473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037222183956231588544315 6055833275934347382816473)
        ·
          refine ⟨4541874956950760537112355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6055833275934347382816473 4541874956950760537112355)
          ·
            refine ⟨6812812435426140805668533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541874956950760537112355 6812812435426140805668533)
            ·
              refine ⟨638701165821200700531425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6812812435426140805668533 638701165821200700531425)
              ·
                refine ⟨479025874365900525398569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638701165821200700531425 479025874365900525398569)
                ·
                  refine ⟨359269405774425394048927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479025874365900525398569 359269405774425394048927)
                  ·
                    rfl

theorem cell20_787134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_787134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787134 prefixEnd_787134 := by exact prefixLift 787134
  have htrace : WordTrace (prefixWord ++ tailWord_787134) baseStart_787134 baseEnd_787134 := by
    simpa [prefixWord, tailWord_787134, baseEnd_787134] using wordTrace_append hprefix tailTrace_787134
  have hstable : (prefixWord ++ tailWord_787134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787134).length < 2 ^ (prefixWord ++ tailWord_787134).sum := by decide
  have hdescent : baseEnd_787134 < baseStart_787134 := by decide
  rcases family_descends (prefixWord ++ tailWord_787134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787148 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_787148 : Nat := 118140960795 + 787148 * 2 ^ 59
def prefixEnd_787148 : Nat := 4983230072969 + 3 ^ 40 * 787148 * 2
def baseEnd_787148 : Nat := 359275795755903567582203

theorem tailTrace_787148 : CollatzResearch.WordTrace tailWord_787148 prefixEnd_787148 359275795755903567582203 := by
  unfold tailWord_787148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14354823076152352510329049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19139764101536470013772065 14354823076152352510329049)
  ·
    refine ⟨10766117307114264382746787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14354823076152352510329049 10766117307114264382746787)
    ·
      refine ⟨16149175960671396574120181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766117307114264382746787 16149175960671396574120181)
      ·
        refine ⟨1513985246312943428823767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16149175960671396574120181 1513985246312943428823767)
        ·
          refine ⟨2270977869469415143235651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513985246312943428823767 2270977869469415143235651)
          ·
            refine ⟨3406466804204122714853477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270977869469415143235651 3406466804204122714853477)
            ·
              refine ⟨638712525788273009035027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3406466804204122714853477 638712525788273009035027)
              ·
                refine ⟨958068788682409513552541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638712525788273009035027 958068788682409513552541)
                ·
                  refine ⟨359275795755903567582203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958068788682409513552541 359275795755903567582203)
                  ·
                    rfl

theorem cell20_787148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_787148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787148 prefixEnd_787148 := by exact prefixLift 787148
  have htrace : WordTrace (prefixWord ++ tailWord_787148) baseStart_787148 baseEnd_787148 := by
    simpa [prefixWord, tailWord_787148, baseEnd_787148] using wordTrace_append hprefix tailTrace_787148
  have hstable : (prefixWord ++ tailWord_787148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787148).length < 2 ^ (prefixWord ++ tailWord_787148).sum := by decide
  have hdescent : baseEnd_787148 < baseStart_787148 := by decide
  rcases family_descends (prefixWord ++ tailWord_787148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787197 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_787197 : Nat := 118140960795 + 787197 * 2 ^ 59
def prefixEnd_787197 : Nat := 4983230072969 + 3 ^ 40 * 787197 * 2
def baseEnd_787197 : Nat := 359298160691077174948669

theorem tailTrace_787197 : CollatzResearch.WordTrace tailWord_787197 prefixEnd_787197 359298160691077174948669 := by
  unfold tailWord_787197
  simp only [CollatzResearch.WordTrace]
  refine ⟨28711433329127186389191845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19140955552751457592794563 28711433329127186389191845)
  ·
    refine ⟨5383393749211347447973471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28711433329127186389191845 5383393749211347447973471)
    ·
      refine ⟨8075090623817021171960207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5383393749211347447973471 8075090623817021171960207)
      ·
        refine ⟨12112635935725531757940311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8075090623817021171960207 12112635935725531757940311)
        ·
          refine ⟨18168953903588297636910467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12112635935725531757940311 18168953903588297636910467)
          ·
            refine ⟨27253430855382446455365701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18168953903588297636910467 27253430855382446455365701)
            ·
              refine ⟨5110018285384208710381069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27253430855382446455365701 5110018285384208710381069)
              ·
                refine ⟨1916256857019078266392901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5110018285384208710381069 1916256857019078266392901)
                ·
                  refine ⟨359298160691077174948669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916256857019078266392901 359298160691077174948669)
                  ·
                    rfl

theorem cell20_787197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_787197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787197 prefixEnd_787197 := by exact prefixLift 787197
  have htrace : WordTrace (prefixWord ++ tailWord_787197) baseStart_787197 baseEnd_787197 := by
    simpa [prefixWord, tailWord_787197, baseEnd_787197] using wordTrace_append hprefix tailTrace_787197
  have hstable : (prefixWord ++ tailWord_787197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787197).length < 2 ^ (prefixWord ++ tailWord_787197).sum := by decide
  have hdescent : baseEnd_787197 < baseStart_787197 := by decide
  rcases family_descends (prefixWord ++ tailWord_787197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787207 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_787207 : Nat := 118140960795 + 787207 * 2 ^ 59
def prefixEnd_787207 : Nat := 4983230072969 + 3 ^ 40 * 787207 * 2
def baseEnd_787207 : Nat := 359302724963561584615295

theorem tailTrace_787207 : CollatzResearch.WordTrace tailWord_787207 prefixEnd_787207 359302724963561584615295 := by
  unfold tailWord_787207
  simp only [CollatzResearch.WordTrace]
  refine ⟨28711798059090958097055875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141198706060638731370583 28711798059090958097055875)
  ·
    refine ⟨43067697088636437145583813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28711798059090958097055875 43067697088636437145583813)
    ·
      refine ⟨8075193204119331964796965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43067697088636437145583813 8075193204119331964796965)
      ·
        refine ⟨1514098725772374743399431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8075193204119331964796965 1514098725772374743399431)
        ·
          refine ⟨2271148088658562115099147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514098725772374743399431 2271148088658562115099147)
          ·
            refine ⟨3406722132987843172648721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271148088658562115099147 3406722132987843172648721)
            ·
              refine ⟨2555041599740882379486541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406722132987843172648721 2555041599740882379486541)
              ·
                refine ⟨958140599902830892307453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2555041599740882379486541 958140599902830892307453)
                ·
                  refine ⟨359302724963561584615295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958140599902830892307453 359302724963561584615295)
                  ·
                    rfl

theorem cell20_787207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_787207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787207 prefixEnd_787207 := by exact prefixLift 787207
  have htrace : WordTrace (prefixWord ++ tailWord_787207) baseStart_787207 baseEnd_787207 := by
    simpa [prefixWord, tailWord_787207, baseEnd_787207] using wordTrace_append hprefix tailTrace_787207
  have hstable : (prefixWord ++ tailWord_787207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787207).length < 2 ^ (prefixWord ++ tailWord_787207).sum := by decide
  have hdescent : baseEnd_787207 < baseStart_787207 := by decide
  rcases family_descends (prefixWord ++ tailWord_787207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787211 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_787211 : Nat := 118140960795 + 787211 * 2 ^ 59
def prefixEnd_787211 : Nat := 4983230072969 + 3 ^ 40 * 787211 * 2
def baseEnd_787211 : Nat := 359304550672555348481945

theorem tailTrace_787211 : CollatzResearch.WordTrace tailWord_787211 prefixEnd_787211 359304550672555348481945 := by
  unfold tailWord_787211
  simp only [CollatzResearch.WordTrace]
  refine ⟨28711943951076466780201487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141295967384311186800991 28711943951076466780201487)
  ·
    refine ⟨43067915926614700170302231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28711943951076466780201487 43067915926614700170302231)
    ·
      refine ⟨64601873889922050255453347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43067915926614700170302231 64601873889922050255453347)
      ·
        refine ⟨96902810834883075383180021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64601873889922050255453347 96902810834883075383180021)
        ·
          refine ⟨9084638515770288317173127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96902810834883075383180021 9084638515770288317173127)
          ·
            refine ⟨13626957773655432475759691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084638515770288317173127 13626957773655432475759691)
            ·
              refine ⟨20440436660483148713639537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626957773655432475759691 20440436660483148713639537)
              ·
                refine ⟨15330327495362361535229653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20440436660483148713639537 15330327495362361535229653)
                ·
                  refine ⟨359304550672555348481945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15330327495362361535229653 359304550672555348481945)
                  ·
                    rfl

theorem cell20_787211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_787211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787211 prefixEnd_787211 := by exact prefixLift 787211
  have htrace : WordTrace (prefixWord ++ tailWord_787211) baseStart_787211 baseEnd_787211 := by
    simpa [prefixWord, tailWord_787211, baseEnd_787211] using wordTrace_append hprefix tailTrace_787211
  have hstable : (prefixWord ++ tailWord_787211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787211).length < 2 ^ (prefixWord ++ tailWord_787211).sum := by decide
  have hdescent : baseEnd_787211 < baseStart_787211 := by decide
  rcases family_descends (prefixWord ++ tailWord_787211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787221 : List Nat := [1, 3, 2, 1, 2, 2, 5, 4]
def baseStart_787221 : Nat := 118140960795 + 787221 * 2 ^ 59
def prefixEnd_787221 : Nat := 4983230072969 + 3 ^ 40 * 787221 * 2
def baseEnd_787221 : Nat := 119769704981679919382857

theorem tailTrace_787221 : CollatzResearch.WordTrace tailWord_787221 prefixEnd_787221 119769704981679919382857 := by
  unfold tailWord_787221
  simp only [CollatzResearch.WordTrace]
  refine ⟨28712308681040238488065517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141539120693492325377011 28712308681040238488065517)
  ·
    refine ⟨10767115755390089433024569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28712308681040238488065517 10767115755390089433024569)
    ·
      refine ⟨8075336816542567074768427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10767115755390089433024569 8075336816542567074768427)
      ·
        refine ⟨12113005224813850612152641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8075336816542567074768427 12113005224813850612152641)
        ·
          refine ⟨9084753918610387959114481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12113005224813850612152641 9084753918610387959114481)
          ·
            refine ⟨6813565438957790969335861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9084753918610387959114481 6813565438957790969335861)
            ·
              refine ⟨638771759902292903375237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6813565438957790969335861 638771759902292903375237)
              ·
                refine ⟨119769704981679919382857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 638771759902292903375237 119769704981679919382857)
                ·
                  rfl

theorem cell20_787221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_787221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787221 prefixEnd_787221 := by exact prefixLift 787221
  have htrace : WordTrace (prefixWord ++ tailWord_787221) baseStart_787221 baseEnd_787221 := by
    simpa [prefixWord, tailWord_787221, baseEnd_787221] using wordTrace_append hprefix tailTrace_787221
  have hstable : (prefixWord ++ tailWord_787221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787221).length < 2 ^ (prefixWord ++ tailWord_787221).sum := by decide
  have hdescent : baseEnd_787221 < baseStart_787221 := by decide
  rcases family_descends (prefixWord ++ tailWord_787221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787231 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 2]
def baseStart_787231 : Nat := 118140960795 + 787231 * 2 ^ 59
def prefixEnd_787231 : Nat := 4983230072969 + 3 ^ 40 * 787231 * 2
def baseEnd_787231 : Nat := 359313679217524167815197

theorem tailTrace_787231 : CollatzResearch.WordTrace tailWord_787231 prefixEnd_787231 359313679217524167815197 := by
  unfold tailWord_787231
  simp only [CollatzResearch.WordTrace]
  refine ⟨28712673411004010195929547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141782274002673463953031 28712673411004010195929547)
  ·
    refine ⟨43069010116506015293894321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28712673411004010195929547 43069010116506015293894321)
    ·
      refine ⟨32301757587379511470420741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43069010116506015293894321 32301757587379511470420741)
      ·
        refine ⟨6056579547633658400703889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32301757587379511470420741 6056579547633658400703889)
        ·
          refine ⟨4542434660725243800527917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6056579547633658400703889 4542434660725243800527917)
          ·
            refine ⟨1703412997771966425197969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4542434660725243800527917 1703412997771966425197969)
            ·
              refine ⟨1277559748328974818898477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703412997771966425197969 1277559748328974818898477)
              ·
                refine ⟨479084905623365557086929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1277559748328974818898477 479084905623365557086929)
                ·
                  refine ⟨359313679217524167815197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479084905623365557086929 359313679217524167815197)
                  ·
                    rfl

theorem cell20_787231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 2].length) (baseStart_787231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787231 prefixEnd_787231 := by exact prefixLift 787231
  have htrace : WordTrace (prefixWord ++ tailWord_787231) baseStart_787231 baseEnd_787231 := by
    simpa [prefixWord, tailWord_787231, baseEnd_787231] using wordTrace_append hprefix tailTrace_787231
  have hstable : (prefixWord ++ tailWord_787231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787231).length < 2 ^ (prefixWord ++ tailWord_787231).sum := by decide
  have hdescent : baseEnd_787231 < baseStart_787231 := by decide
  rcases family_descends (prefixWord ++ tailWord_787231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787273 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_787273 : Nat := 118140960795 + 787273 * 2 ^ 59
def prefixEnd_787273 : Nat := 4983230072969 + 3 ^ 40 * 787273 * 2
def baseEnd_787273 : Nat := 359332849161958688415025

theorem tailTrace_787273 : CollatzResearch.WordTrace tailWord_787273 prefixEnd_787273 359332849161958688415025 := by
  unfold tailWord_787273
  simp only [CollatzResearch.WordTrace]
  refine ⟨28714205276851851368958473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19142803517901234245972315 28714205276851851368958473)
  ·
    refine ⟨21535653957638888526718855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28714205276851851368958473 21535653957638888526718855)
    ·
      refine ⟨32303480936458332790078283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21535653957638888526718855 32303480936458332790078283)
      ·
        refine ⟨48455221404687499185117425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32303480936458332790078283 48455221404687499185117425)
        ·
          refine ⟨36341416053515624388838069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48455221404687499185117425 36341416053515624388838069)
          ·
            refine ⟨3407007755017089786453569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36341416053515624388838069 3407007755017089786453569)
            ·
              refine ⟨2555255816262817339840177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407007755017089786453569 2555255816262817339840177)
              ·
                refine ⟨1916441862197113004880133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555255816262817339840177 1916441862197113004880133)
                ·
                  refine ⟨359332849161958688415025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916441862197113004880133 359332849161958688415025)
                  ·
                    rfl

theorem cell20_787273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_787273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787273 prefixEnd_787273 := by exact prefixLift 787273
  have htrace : WordTrace (prefixWord ++ tailWord_787273) baseStart_787273 baseEnd_787273 := by
    simpa [prefixWord, tailWord_787273, baseEnd_787273] using wordTrace_append hprefix tailTrace_787273
  have hstable : (prefixWord ++ tailWord_787273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787273).length < 2 ^ (prefixWord ++ tailWord_787273).sum := by decide
  have hdescent : baseEnd_787273 < baseStart_787273 := by decide
  rcases family_descends (prefixWord ++ tailWord_787273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787276 : List Nat := [2, 2, 1, 3, 3, 3, 2, 4]
def baseStart_787276 : Nat := 118140960795 + 787276 * 2 ^ 59
def prefixEnd_787276 : Nat := 4983230072969 + 3 ^ 40 * 787276 * 2
def baseEnd_787276 : Nat := 119778072814568003771671

theorem tailTrace_787276 : CollatzResearch.WordTrace tailWord_787276 prefixEnd_787276 119778072814568003771671 := by
  unfold tailWord_787276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357157347920491440658841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19142876463893988587545121 14357157347920491440658841)
  ·
    refine ⟨10767868010940368580494131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14357157347920491440658841 10767868010940368580494131)
    ·
      refine ⟨16151802016410552870741197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10767868010940368580494131 16151802016410552870741197)
      ·
        refine ⟨6056925756153957326527949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16151802016410552870741197 6056925756153957326527949)
        ·
          refine ⟨2271347158557733997447981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6056925756153957326527949 2271347158557733997447981)
          ·
            refine ⟨851755184459150249042993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2271347158557733997447981 851755184459150249042993)
            ·
              refine ⟨638816388344362686782245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851755184459150249042993 638816388344362686782245)
              ·
                refine ⟨119778072814568003771671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 638816388344362686782245 119778072814568003771671)
                ·
                  rfl

theorem cell20_787276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_787276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787276 prefixEnd_787276 := by exact prefixLift 787276
  have htrace : WordTrace (prefixWord ++ tailWord_787276) baseStart_787276 baseEnd_787276 := by
    simpa [prefixWord, tailWord_787276, baseEnd_787276] using wordTrace_append hprefix tailTrace_787276
  have hstable : (prefixWord ++ tailWord_787276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787276).length < 2 ^ (prefixWord ++ tailWord_787276).sum := by decide
  have hdescent : baseEnd_787276 < baseStart_787276 := by decide
  rcases family_descends (prefixWord ++ tailWord_787276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787304 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_787304 : Nat := 118140960795 + 787304 * 2 ^ 59
def prefixEnd_787304 : Nat := 4983230072969 + 3 ^ 40 * 787304 * 2
def baseEnd_787304 : Nat := 359346998406660358381565

theorem tailTrace_787304 : CollatzResearch.WordTrace tailWord_787304 prefixEnd_787304 359346998406660358381565 := by
  unfold tailWord_787304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357667969869771831668483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19143557293159695775557977 14357667969869771831668483)
  ·
    refine ⟨21536501954804657747502725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14357667969869771831668483 21536501954804657747502725)
    ·
      refine ⟨4038094116525873327656761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21536501954804657747502725 4038094116525873327656761)
      ·
        refine ⟨3028570587394404995742571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038094116525873327656761 3028570587394404995742571)
        ·
          refine ⟨4542855881091607493613857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028570587394404995742571 4542855881091607493613857)
          ·
            refine ⟨3407141910818705620210393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4542855881091607493613857 3407141910818705620210393)
            ·
              refine ⟨2555356433114029215157795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407141910818705620210393 2555356433114029215157795)
              ·
                refine ⟨3833034649671043822736693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555356433114029215157795 3833034649671043822736693)
                ·
                  refine ⟨359346998406660358381565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3833034649671043822736693 359346998406660358381565)
                  ·
                    rfl

theorem cell20_787304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_787304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787304 prefixEnd_787304 := by exact prefixLift 787304
  have htrace : WordTrace (prefixWord ++ tailWord_787304) baseStart_787304 baseEnd_787304 := by
    simpa [prefixWord, tailWord_787304, baseEnd_787304] using wordTrace_append hprefix tailTrace_787304
  have hstable : (prefixWord ++ tailWord_787304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787304).length < 2 ^ (prefixWord ++ tailWord_787304).sum := by decide
  have hdescent : baseEnd_787304 < baseStart_787304 := by decide
  rcases family_descends (prefixWord ++ tailWord_787304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787321 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 3]
def baseStart_787321 : Nat := 118140960795 + 787321 * 2 ^ 59
def prefixEnd_787321 : Nat := 4983230072969 + 3 ^ 40 * 787321 * 2
def baseEnd_787321 : Nat := 359354757669883854814829

theorem tailTrace_787321 : CollatzResearch.WordTrace tailWord_787321 prefixEnd_787321 359354757669883854814829 := by
  unfold tailWord_787321
  simp only [CollatzResearch.WordTrace]
  refine ⟨28715955980677955566705817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19143970653785303711137211 28715955980677955566705817)
  ·
    refine ⟨21536966985508466675029363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28715955980677955566705817 21536966985508466675029363)
    ·
      refine ⟨32305450478262700012544045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21536966985508466675029363 32305450478262700012544045)
      ·
        refine ⟨12114543929348512504704017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32305450478262700012544045 12114543929348512504704017)
        ·
          refine ⟨9085907947011384378528013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12114543929348512504704017 9085907947011384378528013)
          ·
            refine ⟨3407215480129269141948005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9085907947011384378528013 3407215480129269141948005)
            ·
              refine ⟨638852902524237964115251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3407215480129269141948005 638852902524237964115251)
              ·
                refine ⟨958279353786356946172877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638852902524237964115251 958279353786356946172877)
                ·
                  refine ⟨359354757669883854814829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958279353786356946172877 359354757669883854814829)
                  ·
                    rfl

theorem cell20_787321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_787321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787321 prefixEnd_787321 := by exact prefixLift 787321
  have htrace : WordTrace (prefixWord ++ tailWord_787321) baseStart_787321 baseEnd_787321 := by
    simpa [prefixWord, tailWord_787321, baseEnd_787321] using wordTrace_append hprefix tailTrace_787321
  have hstable : (prefixWord ++ tailWord_787321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787321).length < 2 ^ (prefixWord ++ tailWord_787321).sum := by decide
  have hdescent : baseEnd_787321 < baseStart_787321 := by decide
  rcases family_descends (prefixWord ++ tailWord_787321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787356 : List Nat := [2, 2, 3, 3, 10]
def baseStart_787356 : Nat := 118140960795 + 787356 * 2 ^ 59
def prefixEnd_787356 : Nat := 4983230072969 + 3 ^ 40 * 787356 * 2
def baseEnd_787356 : Nat := 4436675711402213440099

theorem tailTrace_787356 : CollatzResearch.WordTrace tailWord_787356 prefixEnd_787356 4436675711402213440099 := by
  unfold tailWord_787356
  simp only [CollatzResearch.WordTrace]
  refine ⟨14358616267775578272114961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19144821690367437696153281 14358616267775578272114961)
  ·
    refine ⟨10768962200831683704086221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14358616267775578272114961 10768962200831683704086221)
    ·
      refine ⟨4038360825311881389032333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10768962200831683704086221 4038360825311881389032333)
      ·
        refine ⟨1514385309491955520887125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4038360825311881389032333 1514385309491955520887125)
        ·
          refine ⟨4436675711402213440099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1514385309491955520887125 4436675711402213440099)
          ·
            rfl

theorem cell20_787356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 10].length) (baseStart_787356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787356 prefixEnd_787356 := by exact prefixLift 787356
  have htrace : WordTrace (prefixWord ++ tailWord_787356) baseStart_787356 baseEnd_787356 := by
    simpa [prefixWord, tailWord_787356, baseEnd_787356] using wordTrace_append hprefix tailTrace_787356
  have hstable : (prefixWord ++ tailWord_787356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787356).length < 2 ^ (prefixWord ++ tailWord_787356).sum := by decide
  have hdescent : baseEnd_787356 < baseStart_787356 := by decide
  rcases family_descends (prefixWord ++ tailWord_787356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787359 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_787359 : Nat := 118140960795 + 787359 * 2 ^ 59
def prefixEnd_787359 : Nat := 4983230072969 + 3 ^ 40 * 787359 * 2
def baseEnd_787359 : Nat := 359372101905324611548007

theorem tailTrace_787359 : CollatzResearch.WordTrace tailWord_787359 prefixEnd_787359 359372101905324611548007 := by
  unfold tailWord_787359
  simp only [CollatzResearch.WordTrace]
  refine ⟨28717341954540288056589131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19144894636360192037726087 28717341954540288056589131)
  ·
    refine ⟨43076012931810432084883697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28717341954540288056589131 43076012931810432084883697)
    ·
      refine ⟨32307009698857824063662773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43076012931810432084883697 32307009698857824063662773)
      ·
        refine ⟨3028782159267921005968385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32307009698857824063662773 3028782159267921005968385)
        ·
          refine ⟨2271586619450940754476289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3028782159267921005968385 2271586619450940754476289)
          ·
            refine ⟨1703689964588205565857217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271586619450940754476289 1703689964588205565857217)
            ·
              refine ⟨1277767473441154174392913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703689964588205565857217 1277767473441154174392913)
              ·
                refine ⟨958325605080865630794685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277767473441154174392913 958325605080865630794685)
                ·
                  refine ⟨359372101905324611548007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958325605080865630794685 359372101905324611548007)
                  ·
                    rfl

theorem cell20_787359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_787359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787359 prefixEnd_787359 := by exact prefixLift 787359
  have htrace : WordTrace (prefixWord ++ tailWord_787359) baseStart_787359 baseEnd_787359 := by
    simpa [prefixWord, tailWord_787359, baseEnd_787359] using wordTrace_append hprefix tailTrace_787359
  have hstable : (prefixWord ++ tailWord_787359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787359).length < 2 ^ (prefixWord ++ tailWord_787359).sum := by decide
  have hdescent : baseEnd_787359 < baseStart_787359 := by decide
  rcases family_descends (prefixWord ++ tailWord_787359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787362 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_787362 : Nat := 118140960795 + 787362 * 2 ^ 59
def prefixEnd_787362 : Nat := 4983230072969 + 3 ^ 40 * 787362 * 2
def baseEnd_787362 : Nat := 359373471187069934447995

theorem tailTrace_787362 : CollatzResearch.WordTrace tailWord_787362 prefixEnd_787362 359373471187069934447995 := by
  unfold tailWord_787362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179362843382354892237085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19144967582352946379298893 7179362843382354892237085)
  ·
    refine ⟨2692261066268383084588907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7179362843382354892237085 2692261066268383084588907)
    ·
      refine ⟨4038391599402574626883361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692261066268383084588907 4038391599402574626883361)
      ·
        refine ⟨3028793699551930970162521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038391599402574626883361 3028793699551930970162521)
        ·
          refine ⟨2271595274663948227621891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3028793699551930970162521 2271595274663948227621891)
          ·
            refine ⟨3407392911995922341432837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271595274663948227621891 3407392911995922341432837)
            ·
              refine ⟨638886170999235439018657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3407392911995922341432837 638886170999235439018657)
              ·
                refine ⟨479164628249426579263993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638886170999235439018657 479164628249426579263993)
                ·
                  refine ⟨359373471187069934447995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479164628249426579263993 359373471187069934447995)
                  ·
                    rfl

theorem cell20_787362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_787362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787362 prefixEnd_787362 := by exact prefixLift 787362
  have htrace : WordTrace (prefixWord ++ tailWord_787362) baseStart_787362 baseEnd_787362 := by
    simpa [prefixWord, tailWord_787362, baseEnd_787362] using wordTrace_append hprefix tailTrace_787362
  have hstable : (prefixWord ++ tailWord_787362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787362).length < 2 ^ (prefixWord ++ tailWord_787362).sum := by decide
  have hdescent : baseEnd_787362 < baseStart_787362 := by decide
  rcases family_descends (prefixWord ++ tailWord_787362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787363 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_787363 : Nat := 118140960795 + 787363 * 2 ^ 59
def prefixEnd_787363 : Nat := 4983230072969 + 3 ^ 40 * 787363 * 2
def baseEnd_787363 : Nat := 359373927614318375414657

theorem tailTrace_787363 : CollatzResearch.WordTrace tailWord_787363 prefixEnd_787363 359373927614318375414657 := by
  unfold tailWord_787363
  simp only [CollatzResearch.WordTrace]
  refine ⟨28717487846525796739734743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19144991897683864493156495 28717487846525796739734743)
  ·
    refine ⟨43076231769788695109602115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28717487846525796739734743 43076231769788695109602115)
    ·
      refine ⟨64614347654683042664403173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43076231769788695109602115 64614347654683042664403173)
      ·
        refine ⟨12115190185253070499575595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64614347654683042664403173 12115190185253070499575595)
        ·
          refine ⟨18172785277879605749363393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12115190185253070499575595 18172785277879605749363393)
          ·
            refine ⟨13629588958409704312022545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18172785277879605749363393 13629588958409704312022545)
            ·
              refine ⟨10222191718807278234016909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13629588958409704312022545 10222191718807278234016909)
              ·
                refine ⟨3833321894552729337756341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10222191718807278234016909 3833321894552729337756341)
                ·
                  refine ⟨359373927614318375414657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3833321894552729337756341 359373927614318375414657)
                  ·
                    rfl

theorem cell20_787363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_787363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787363 prefixEnd_787363 := by exact prefixLift 787363
  have htrace : WordTrace (prefixWord ++ tailWord_787363) baseStart_787363 baseEnd_787363 := by
    simpa [prefixWord, tailWord_787363, baseEnd_787363] using wordTrace_append hprefix tailTrace_787363
  have hstable : (prefixWord ++ tailWord_787363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787363).length < 2 ^ (prefixWord ++ tailWord_787363).sum := by decide
  have hdescent : baseEnd_787363 < baseStart_787363 := by decide
  rcases family_descends (prefixWord ++ tailWord_787363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787408 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_787408 : Nat := 118140960795 + 787408 * 2 ^ 59
def prefixEnd_787408 : Nat := 4983230072969 + 3 ^ 40 * 787408 * 2
def baseEnd_787408 : Nat := 359394466840498218914473

theorem tailTrace_787408 : CollatzResearch.WordTrace tailWord_787408 prefixEnd_787408 359394466840498218914473 := by
  unfold tailWord_787408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14359564565681384712561439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19146086087575179616748585 14359564565681384712561439)
  ·
    refine ⟨21539346848522077068842159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14359564565681384712561439 21539346848522077068842159)
    ·
      refine ⟨32309020272783115603263239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21539346848522077068842159 32309020272783115603263239)
      ·
        refine ⟨48463530409174673404894859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32309020272783115603263239 48463530409174673404894859)
        ·
          refine ⟨72695295613762010107342289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48463530409174673404894859 72695295613762010107342289)
          ·
            refine ⟨54521471710321507580506717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72695295613762010107342289 54521471710321507580506717)
            ·
              refine ⟨20445551891370565342690019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54521471710321507580506717 20445551891370565342690019)
              ·
                refine ⟨30668327837055848014035029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20445551891370565342690019 30668327837055848014035029)
                ·
                  refine ⟨359394466840498218914473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30668327837055848014035029 359394466840498218914473)
                  ·
                    rfl

theorem cell20_787408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_787408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787408 prefixEnd_787408 := by exact prefixLift 787408
  have htrace : WordTrace (prefixWord ++ tailWord_787408) baseStart_787408 baseEnd_787408 := by
    simpa [prefixWord, tailWord_787408, baseEnd_787408] using wordTrace_append hprefix tailTrace_787408
  have hstable : (prefixWord ++ tailWord_787408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787408).length < 2 ^ (prefixWord ++ tailWord_787408).sum := by decide
  have hdescent : baseEnd_787408 < baseStart_787408 := by decide
  rcases family_descends (prefixWord ++ tailWord_787408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787414 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_787414 : Nat := 118140960795 + 787414 * 2 ^ 59
def prefixEnd_787414 : Nat := 4983230072969 + 3 ^ 40 * 787414 * 2
def baseEnd_787414 : Nat := 359397205403988864714449

theorem tailTrace_787414 : CollatzResearch.WordTrace tailWord_787414 prefixEnd_787414 359397205403988864714449 := by
  unfold tailWord_787414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794959248083814528115081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19146231979560688299894197 1794959248083814528115081)
  ·
    refine ⟨1346219436062860896086311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1794959248083814528115081 1346219436062860896086311)
    ·
      refine ⟨2019329154094291344129467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346219436062860896086311 2019329154094291344129467)
      ·
        refine ⟨3028993731141437016194201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019329154094291344129467 3028993731141437016194201)
        ·
          refine ⟨2271745298356077762145651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3028993731141437016194201 2271745298356077762145651)
          ·
            refine ⟨3407617947534116643218477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271745298356077762145651 3407617947534116643218477)
            ·
              refine ⟨1277856730325293741206929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3407617947534116643218477 1277856730325293741206929)
              ·
                refine ⟨958392547743970305905197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277856730325293741206929 958392547743970305905197)
                ·
                  refine ⟨359397205403988864714449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958392547743970305905197 359397205403988864714449)
                  ·
                    rfl

theorem cell20_787414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_787414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787414 prefixEnd_787414 := by exact prefixLift 787414
  have htrace : WordTrace (prefixWord ++ tailWord_787414) baseStart_787414 baseEnd_787414 := by
    simpa [prefixWord, tailWord_787414, baseEnd_787414] using wordTrace_append hprefix tailTrace_787414
  have hstable : (prefixWord ++ tailWord_787414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787414).length < 2 ^ (prefixWord ++ tailWord_787414).sum := by decide
  have hdescent : baseEnd_787414 < baseStart_787414 := by decide
  rcases family_descends (prefixWord ++ tailWord_787414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787418 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_787418 : Nat := 118140960795 + 787418 * 2 ^ 59
def prefixEnd_787418 : Nat := 4983230072969 + 3 ^ 40 * 787418 * 2
def baseEnd_787418 : Nat := 359399031112982628581099

theorem tailTrace_787418 : CollatzResearch.WordTrace tailWord_787418 prefixEnd_787418 359399031112982628581099 := by
  unfold tailWord_787418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179873465331635283246727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19146329240884360755324605 7179873465331635283246727)
  ·
    refine ⟨10769810197997452924870091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7179873465331635283246727 10769810197997452924870091)
    ·
      refine ⟨16154715296996179387305137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10769810197997452924870091 16154715296996179387305137)
      ·
        refine ⟨12116036472747134540478853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16154715296996179387305137 12116036472747134540478853)
        ·
          refine ⟨2271756838640087726339785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12116036472747134540478853 2271756838640087726339785)
          ·
            refine ⟨1703817628980065794754839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271756838640087726339785 1703817628980065794754839)
            ·
              refine ⟨2555726443470098692132259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703817628980065794754839 2555726443470098692132259)
              ·
                refine ⟨3833589665205148038198389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555726443470098692132259 3833589665205148038198389)
                ·
                  refine ⟨359399031112982628581099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3833589665205148038198389 359399031112982628581099)
                  ·
                    rfl

theorem cell20_787418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_787418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787418 prefixEnd_787418 := by exact prefixLift 787418
  have htrace : WordTrace (prefixWord ++ tailWord_787418) baseStart_787418 baseEnd_787418 := by
    simpa [prefixWord, tailWord_787418, baseEnd_787418] using wordTrace_append hprefix tailTrace_787418
  have hstable : (prefixWord ++ tailWord_787418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787418).length < 2 ^ (prefixWord ++ tailWord_787418).sum := by decide
  have hdescent : baseEnd_787418 < baseStart_787418 := by decide
  rcases family_descends (prefixWord ++ tailWord_787418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787421 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 2]
def baseStart_787421 : Nat := 118140960795 + 787421 * 2 ^ 59
def prefixEnd_787421 : Nat := 4983230072969 + 3 ^ 40 * 787421 * 2
def baseEnd_787421 : Nat := 359400400394727951481087

theorem tailTrace_787421 : CollatzResearch.WordTrace tailWord_787421 prefixEnd_787421 359400400394727951481087 := by
  unfold tailWord_787421
  simp only [CollatzResearch.WordTrace]
  refine ⟨28719603280315672645346117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19146402186877115096897411 28719603280315672645346117)
  ·
    refine ⟨5384925615059188621002397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28719603280315672645346117 5384925615059188621002397)
    ·
      refine ⟨2019347105647195732875899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5384925615059188621002397 2019347105647195732875899)
      ·
        refine ⟨3029020658470793599313849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019347105647195732875899 3029020658470793599313849)
        ·
          refine ⟨2271765493853095199485387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3029020658470793599313849 2271765493853095199485387)
          ·
            refine ⟨3407648240779642799228081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271765493853095199485387 3407648240779642799228081)
            ·
              refine ⟨2555736180584732099421061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407648240779642799228081 2555736180584732099421061)
              ·
                refine ⟨479200533859637268641449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2555736180584732099421061 479200533859637268641449)
                ·
                  refine ⟨359400400394727951481087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479200533859637268641449 359400400394727951481087)
                  ·
                    rfl

theorem cell20_787421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_787421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787421 prefixEnd_787421 := by exact prefixLift 787421
  have htrace : WordTrace (prefixWord ++ tailWord_787421) baseStart_787421 baseEnd_787421 := by
    simpa [prefixWord, tailWord_787421, baseEnd_787421] using wordTrace_append hprefix tailTrace_787421
  have hstable : (prefixWord ++ tailWord_787421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787421).length < 2 ^ (prefixWord ++ tailWord_787421).sum := by decide
  have hdescent : baseEnd_787421 < baseStart_787421 := by decide
  rcases family_descends (prefixWord ++ tailWord_787421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787470 : List Nat := [4, 1, 1, 2, 2, 2, 8]
def baseStart_787470 : Nat := 118140960795 + 787470 * 2 ^ 59
def prefixEnd_787470 : Nat := 4983230072969 + 3 ^ 40 * 787470 * 2
def baseEnd_787470 : Nat := 39935862814433506538617

theorem tailTrace_787470 : CollatzResearch.WordTrace tailWord_787470 prefixEnd_787470 39935862814433506538617 := by
  unfold tailWord_787470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590173807142269251734983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19147593638092102675919909 3590173807142269251734983)
  ·
    refine ⟨5385260710713403877602475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3590173807142269251734983 5385260710713403877602475)
    ·
      refine ⟨8077891066070105816403713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5385260710713403877602475 8077891066070105816403713)
      ·
        refine ⟨6058418299552579362302785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8077891066070105816403713 6058418299552579362302785)
        ·
          refine ⟨4543813724664434521727089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6058418299552579362302785 4543813724664434521727089)
          ·
            refine ⟨3407860293498325891295317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4543813724664434521727089 3407860293498325891295317)
            ·
              refine ⟨39935862814433506538617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3407860293498325891295317 39935862814433506538617)
              ·
                rfl

theorem cell20_787470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_787470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787470 prefixEnd_787470 := by exact prefixLift 787470
  have htrace : WordTrace (prefixWord ++ tailWord_787470) baseStart_787470 baseEnd_787470 := by
    simpa [prefixWord, tailWord_787470, baseEnd_787470] using wordTrace_append hprefix tailTrace_787470
  have hstable : (prefixWord ++ tailWord_787470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787470).length < 2 ^ (prefixWord ++ tailWord_787470).sum := by decide
  have hdescent : baseEnd_787470 < baseStart_787470 := by decide
  rcases family_descends (prefixWord ++ tailWord_787470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787480 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_787480 : Nat := 118140960795 + 787480 * 2 ^ 59
def prefixEnd_787480 : Nat := 4983230072969 + 3 ^ 40 * 787480 * 2
def baseEnd_787480 : Nat := 359427329602385968514179

theorem tailTrace_787480 : CollatzResearch.WordTrace tailWord_787480 prefixEnd_787480 359427329602385968514179 := by
  unfold tailWord_787480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14360877593550962860871947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19147836791401283814495929 14360877593550962860871947)
  ·
    refine ⟨21541316390326444291307921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14360877593550962860871947 21541316390326444291307921)
    ·
      refine ⟨16155987292744833218480941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21541316390326444291307921 16155987292744833218480941)
      ·
        refine ⟨6058495234779312456930353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16155987292744833218480941 6058495234779312456930353)
        ·
          refine ⟨4543871426084484342697765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6058495234779312456930353 4543871426084484342697765)
          ·
            refine ⟨851975892390840814255831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4543871426084484342697765 851975892390840814255831)
            ·
              refine ⟨1277963838586261221383747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851975892390840814255831 1277963838586261221383747)
              ·
                refine ⟨1916945757879391832075621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277963838586261221383747 1916945757879391832075621)
                ·
                  refine ⟨359427329602385968514179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916945757879391832075621 359427329602385968514179)
                  ·
                    rfl

theorem cell20_787480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_787480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787480 prefixEnd_787480 := by exact prefixLift 787480
  have htrace : WordTrace (prefixWord ++ tailWord_787480) baseStart_787480 baseEnd_787480 := by
    simpa [prefixWord, tailWord_787480, baseEnd_787480] using wordTrace_append hprefix tailTrace_787480
  have hstable : (prefixWord ++ tailWord_787480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787480).length < 2 ^ (prefixWord ++ tailWord_787480).sum := by decide
  have hdescent : baseEnd_787480 < baseStart_787480 := by decide
  rcases family_descends (prefixWord ++ tailWord_787480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787490 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_787490 : Nat := 118140960795 + 787490 * 2 ^ 59
def prefixEnd_787490 : Nat := 4983230072969 + 3 ^ 40 * 787490 * 2
def baseEnd_787490 : Nat := 359431893874870378180805

theorem tailTrace_787490 : CollatzResearch.WordTrace tailWord_787490 prefixEnd_787490 359431893874870378180805 := by
  unfold tailWord_787490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180529979266424357401981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19148079944710464953071949 7180529979266424357401981)
  ·
    refine ⟨2692698742224909134025743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7180529979266424357401981 2692698742224909134025743)
    ·
      refine ⟨4039048113337363701038615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692698742224909134025743 4039048113337363701038615)
      ·
        refine ⟨6058572170006045551557923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039048113337363701038615 6058572170006045551557923)
        ·
          refine ⟨9087858255009068327336885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058572170006045551557923 9087858255009068327336885)
          ·
            refine ⟨851986711407100155687833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9087858255009068327336885 851986711407100155687833)
            ·
              refine ⟨638990033555325116765875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851986711407100155687833 638990033555325116765875)
              ·
                refine ⟨958485050332987675148813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638990033555325116765875 958485050332987675148813)
                ·
                  refine ⟨359431893874870378180805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958485050332987675148813 359431893874870378180805)
                  ·
                    rfl

theorem cell20_787490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_787490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787490 prefixEnd_787490 := by exact prefixLift 787490
  have htrace : WordTrace (prefixWord ++ tailWord_787490) baseStart_787490 baseEnd_787490 := by
    simpa [prefixWord, tailWord_787490, baseEnd_787490] using wordTrace_append hprefix tailTrace_787490
  have hstable : (prefixWord ++ tailWord_787490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787490).length < 2 ^ (prefixWord ++ tailWord_787490).sum := by decide
  have hdescent : baseEnd_787490 < baseStart_787490 := by decide
  rcases family_descends (prefixWord ++ tailWord_787490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787594 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_787594 : Nat := 118140960795 + 787594 * 2 ^ 59
def prefixEnd_787594 : Nat := 4983230072969 + 3 ^ 40 * 787594 * 2
def baseEnd_787594 : Nat := 359479362308708238713713

theorem tailTrace_787594 : CollatzResearch.WordTrace tailWord_787594 prefixEnd_787594 359479362308708238713713 := by
  unfold tailWord_787594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7181478277172230797848459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19150608739125948794262557 7181478277172230797848459)
  ·
    refine ⟨10772217415758346196772689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7181478277172230797848459 10772217415758346196772689)
    ·
      refine ⟨8079163061818759647579517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10772217415758346196772689 8079163061818759647579517)
      ·
        refine ⟨3029686148182034867842319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8079163061818759647579517 3029686148182034867842319)
        ·
          refine ⟨4544529222273052301763479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029686148182034867842319 4544529222273052301763479)
          ·
            refine ⟨6816793833409578452645219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544529222273052301763479 6816793833409578452645219)
            ·
              refine ⟨10225190750114367678967829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816793833409578452645219 10225190750114367678967829)
              ·
                refine ⟨479305816411610984951617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10225190750114367678967829 479305816411610984951617)
                ·
                  refine ⟨359479362308708238713713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479305816411610984951617 359479362308708238713713)
                  ·
                    rfl

theorem cell20_787594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_787594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787594 prefixEnd_787594 := by exact prefixLift 787594
  have htrace : WordTrace (prefixWord ++ tailWord_787594) baseStart_787594 baseEnd_787594 := by
    simpa [prefixWord, tailWord_787594, baseEnd_787594] using wordTrace_append hprefix tailTrace_787594
  have hstable : (prefixWord ++ tailWord_787594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787594).length < 2 ^ (prefixWord ++ tailWord_787594).sum := by decide
  have hdescent : baseEnd_787594 < baseStart_787594 := by decide
  rcases family_descends (prefixWord ++ tailWord_787594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787646 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_787646 : Nat := 118140960795 + 787646 * 2 ^ 59
def prefixEnd_787646 : Nat := 4983230072969 + 3 ^ 40 * 787646 * 2
def baseEnd_787646 : Nat := 359503096525627168980167

theorem tailTrace_787646 : CollatzResearch.WordTrace tailWord_787646 prefixEnd_787646 359503096525627168980167 := by
  unfold tailWord_787646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590976213062567009035849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19151873136333690714857861 3590976213062567009035849)
  ·
    refine ⟨2693232159796925256776887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3590976213062567009035849 2693232159796925256776887)
    ·
      refine ⟨4039848239695387885165331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693232159796925256776887 4039848239695387885165331)
      ·
        refine ⟨6059772359543081827747997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039848239695387885165331 6059772359543081827747997)
        ·
          refine ⟨2272414634828655685405499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6059772359543081827747997 2272414634828655685405499)
          ·
            refine ⟨3408621952242983528108249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272414634828655685405499 3408621952242983528108249)
            ·
              refine ⟨2556466464182237646081187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408621952242983528108249 2556466464182237646081187)
              ·
                refine ⟨3834699696273356469121781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556466464182237646081187 3834699696273356469121781)
                ·
                  refine ⟨359503096525627168980167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3834699696273356469121781 359503096525627168980167)
                  ·
                    rfl

theorem cell20_787646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_787646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787646 prefixEnd_787646 := by exact prefixLift 787646
  have htrace : WordTrace (prefixWord ++ tailWord_787646) baseStart_787646 baseEnd_787646 := by
    simpa [prefixWord, tailWord_787646, baseEnd_787646] using wordTrace_append hprefix tailTrace_787646
  have hstable : (prefixWord ++ tailWord_787646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787646).length < 2 ^ (prefixWord ++ tailWord_787646).sum := by decide
  have hdescent : baseEnd_787646 < baseStart_787646 := by decide
  rcases family_descends (prefixWord ++ tailWord_787646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787649 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 4]
def baseStart_787649 : Nat := 118140960795 + 787649 * 2 ^ 59
def prefixEnd_787649 : Nat := 4983230072969 + 3 ^ 40 * 787649 * 2
def baseEnd_787649 : Nat := 359504465807372491880155

theorem tailTrace_787649 : CollatzResearch.WordTrace tailWord_787649 prefixEnd_787649 359504465807372491880155 := by
  unfold tailWord_787649
  simp only [CollatzResearch.WordTrace]
  refine ⟨28727919123489667584646001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19151946082326445056430667 28727919123489667584646001)
  ·
    refine ⟨21545939342617250688484501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28727919123489667584646001 21545939342617250688484501)
    ·
      refine ⟨1009965906685183626022711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21545939342617250688484501 1009965906685183626022711)
      ·
        refine ⟨1514948860027775439034067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009965906685183626022711 1514948860027775439034067)
        ·
          refine ⟨2272423290041663158551101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514948860027775439034067 2272423290041663158551101)
          ·
            refine ⟨852158733765623684456663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2272423290041663158551101 852158733765623684456663)
            ·
              refine ⟨1278238100648435526684995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852158733765623684456663 1278238100648435526684995)
              ·
                refine ⟨1917357150972653290027493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278238100648435526684995 1917357150972653290027493)
                ·
                  refine ⟨359504465807372491880155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917357150972653290027493 359504465807372491880155)
                  ·
                    rfl

theorem cell20_787649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_787649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787649 prefixEnd_787649 := by exact prefixLift 787649
  have htrace : WordTrace (prefixWord ++ tailWord_787649) baseStart_787649 baseEnd_787649 := by
    simpa [prefixWord, tailWord_787649, baseEnd_787649] using wordTrace_append hprefix tailTrace_787649
  have hstable : (prefixWord ++ tailWord_787649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787649).length < 2 ^ (prefixWord ++ tailWord_787649).sum := by decide
  have hdescent : baseEnd_787649 < baseStart_787649 := by decide
  rcases family_descends (prefixWord ++ tailWord_787649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787667 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_787667 : Nat := 118140960795 + 787667 * 2 ^ 59
def prefixEnd_787667 : Nat := 4983230072969 + 3 ^ 40 * 787667 * 2
def baseEnd_787667 : Nat := 359512681497844429280081

theorem tailTrace_787667 : CollatzResearch.WordTrace tailWord_787667 prefixEnd_787667 359512681497844429280081 := by
  unfold tailWord_787667
  simp only [CollatzResearch.WordTrace]
  refine ⟨28728575637424456658801255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19152383758282971105867503 28728575637424456658801255)
  ·
    refine ⟨43092863456136684988201883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28728575637424456658801255 43092863456136684988201883)
    ·
      refine ⟨64639295184205027482302825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43092863456136684988201883 64639295184205027482302825)
      ·
        refine ⟨48479471388153770611727119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64639295184205027482302825 48479471388153770611727119)
        ·
          refine ⟨72719207082230655917590679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48479471388153770611727119 72719207082230655917590679)
          ·
            refine ⟨109078810623345983876386019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72719207082230655917590679 109078810623345983876386019)
            ·
              refine ⟨163618215935018975814579029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109078810623345983876386019 163618215935018975814579029)
              ·
                refine ⟨958700483994251811413549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 163618215935018975814579029 958700483994251811413549)
                ·
                  refine ⟨359512681497844429280081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958700483994251811413549 359512681497844429280081)
                  ·
                    rfl

theorem cell20_787667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_787667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787667 prefixEnd_787667 := by exact prefixLift 787667
  have htrace : WordTrace (prefixWord ++ tailWord_787667) baseStart_787667 baseEnd_787667 := by
    simpa [prefixWord, tailWord_787667, baseEnd_787667] using wordTrace_append hprefix tailTrace_787667
  have hstable : (prefixWord ++ tailWord_787667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787667).length < 2 ^ (prefixWord ++ tailWord_787667).sum := by decide
  have hdescent : baseEnd_787667 < baseStart_787667 := by decide
  rcases family_descends (prefixWord ++ tailWord_787667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787674 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_787674 : Nat := 118140960795 + 787674 * 2 ^ 59
def prefixEnd_787674 : Nat := 4983230072969 + 3 ^ 40 * 787674 * 2
def baseEnd_787674 : Nat := 359515876488583516046719

theorem tailTrace_787674 : CollatzResearch.WordTrace tailWord_787674 prefixEnd_787674 359515876488583516046719 := by
  unfold tailWord_787674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182207737099774213576519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19152553965599397902870717 7182207737099774213576519)
  ·
    refine ⟨10773311605649661320364779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7182207737099774213576519 10773311605649661320364779)
    ·
      refine ⟨16159967408474491980547169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773311605649661320364779 16159967408474491980547169)
      ·
        refine ⟨12119975556355868985410377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16159967408474491980547169 12119975556355868985410377)
        ·
          refine ⟨9089981667266901739057783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12119975556355868985410377 9089981667266901739057783)
          ·
            refine ⟨13634972500900352608586675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9089981667266901739057783 13634972500900352608586675)
            ·
              refine ⟨20452458751350528912880013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13634972500900352608586675 20452458751350528912880013)
              ·
                refine ⟨7669672031756448342330005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20452458751350528912880013 7669672031756448342330005)
                ·
                  refine ⟨359515876488583516046719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7669672031756448342330005 359515876488583516046719)
                  ·
                    rfl

theorem cell20_787674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_787674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787674 prefixEnd_787674 := by exact prefixLift 787674
  have htrace : WordTrace (prefixWord ++ tailWord_787674) baseStart_787674 baseEnd_787674 := by
    simpa [prefixWord, tailWord_787674, baseEnd_787674] using wordTrace_append hprefix tailTrace_787674
  have hstable : (prefixWord ++ tailWord_787674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787674).length < 2 ^ (prefixWord ++ tailWord_787674).sum := by decide
  have hdescent : baseEnd_787674 < baseStart_787674 := by decide
  rcases family_descends (prefixWord ++ tailWord_787674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787698 : List Nat := [3, 2, 1, 3, 3, 8]
def baseStart_787698 : Nat := 118140960795 + 787698 * 2 ^ 59
def prefixEnd_787698 : Nat := 4983230072969 + 3 ^ 40 * 787698 * 2
def baseEnd_787698 : Nat := 13315808546020225898023

theorem tailTrace_787698 : CollatzResearch.WordTrace tailWord_787698 prefixEnd_787698 13315808546020225898023 := by
  unfold tailWord_787698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182426575078037238294937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19153137533541432635453165 7182426575078037238294937)
  ·
    refine ⟨5386819931308527928721203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7182426575078037238294937 5386819931308527928721203)
    ·
      refine ⟨8080229896962791893081805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5386819931308527928721203 8080229896962791893081805)
      ·
        refine ⟨3030086211361046959905677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8080229896962791893081805 3030086211361046959905677)
        ·
          refine ⟨1136282329260392609964629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3030086211361046959905677 1136282329260392609964629)
          ·
            refine ⟨13315808546020225898023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1136282329260392609964629 13315808546020225898023)
            ·
              rfl

theorem cell20_787698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 8].length) (baseStart_787698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787698 prefixEnd_787698 := by exact prefixLift 787698
  have htrace : WordTrace (prefixWord ++ tailWord_787698) baseStart_787698 baseEnd_787698 := by
    simpa [prefixWord, tailWord_787698, baseEnd_787698] using wordTrace_append hprefix tailTrace_787698
  have hstable : (prefixWord ++ tailWord_787698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787698).length < 2 ^ (prefixWord ++ tailWord_787698).sum := by decide
  have hdescent : baseEnd_787698 < baseStart_787698 := by decide
  rcases family_descends (prefixWord ++ tailWord_787698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787712 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_787712 : Nat := 118140960795 + 787712 * 2 ^ 59
def prefixEnd_787712 : Nat := 4983230072969 + 3 ^ 40 * 787712 * 2
def baseEnd_787712 : Nat := 359533220724024272779897

theorem tailTrace_787712 : CollatzResearch.WordTrace tailWord_787712 prefixEnd_787712 359533220724024272779897 := by
  unfold tailWord_787712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14365108461130714672094695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19153477948174286229459593 14365108461130714672094695)
  ·
    refine ⟨21547662691696072008142043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14365108461130714672094695 21547662691696072008142043)
    ·
      refine ⟨32321494037544108012213065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21547662691696072008142043 32321494037544108012213065)
      ·
        refine ⟨24241120528158081009159799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32321494037544108012213065 24241120528158081009159799)
        ·
          refine ⟨36361680792237121513739699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24241120528158081009159799 36361680792237121513739699)
          ·
            refine ⟨54542521188355682270609549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36361680792237121513739699 54542521188355682270609549)
            ·
              refine ⟨20453445445633380851478581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54542521188355682270609549 20453445445633380851478581)
              ·
                refine ⟨1917510510528129454826117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20453445445633380851478581 1917510510528129454826117)
                ·
                  refine ⟨359533220724024272779897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917510510528129454826117 359533220724024272779897)
                  ·
                    rfl

theorem cell20_787712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_787712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787712 prefixEnd_787712 := by exact prefixLift 787712
  have htrace : WordTrace (prefixWord ++ tailWord_787712) baseStart_787712 baseEnd_787712 := by
    simpa [prefixWord, tailWord_787712, baseEnd_787712] using wordTrace_append hprefix tailTrace_787712
  have hstable : (prefixWord ++ tailWord_787712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787712).length < 2 ^ (prefixWord ++ tailWord_787712).sum := by decide
  have hdescent : baseEnd_787712 < baseStart_787712 := by decide
  rcases family_descends (prefixWord ++ tailWord_787712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787774 : List Nat := [4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_787774 : Nat := 118140960795 + 787774 * 2 ^ 59
def prefixEnd_787774 : Nat := 4983230072969 + 3 ^ 40 * 787774 * 2
def baseEnd_787774 : Nat := 119853839737809204237659

theorem tailTrace_787774 : CollatzResearch.WordTrace tailWord_787774 prefixEnd_787774 119853839737809204237659 := by
  unfold tailWord_787774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591559781004601741618297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19154985498691209288630917 3591559781004601741618297)
  ·
    refine ⟨2693669835753451306213723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3591559781004601741618297 2693669835753451306213723)
    ·
      refine ⟨4040504753630176959320585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693669835753451306213723 4040504753630176959320585)
      ·
        refine ⟨3030378565222632719490439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4040504753630176959320585 3030378565222632719490439)
        ·
          refine ⟨4545567847833949079235659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030378565222632719490439 4545567847833949079235659)
          ·
            refine ⟨6818351771750923618853489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545567847833949079235659 6818351771750923618853489)
            ·
              refine ⟨5113763828813192714140117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6818351771750923618853489 5113763828813192714140117)
              ·
                refine ⟨119853839737809204237659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5113763828813192714140117 119853839737809204237659)
                ·
                  rfl

theorem cell20_787774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_787774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787774 prefixEnd_787774 := by exact prefixLift 787774
  have htrace : WordTrace (prefixWord ++ tailWord_787774) baseStart_787774 baseEnd_787774 := by
    simpa [prefixWord, tailWord_787774, baseEnd_787774] using wordTrace_append hprefix tailTrace_787774
  have hstable : (prefixWord ++ tailWord_787774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787774).length < 2 ^ (prefixWord ++ tailWord_787774).sum := by decide
  have hdescent : baseEnd_787774 < baseStart_787774 := by decide
  rcases family_descends (prefixWord ++ tailWord_787774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787781 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_787781 : Nat := 118140960795 + 787781 * 2 ^ 59
def prefixEnd_787781 : Nat := 4983230072969 + 3 ^ 40 * 787781 * 2
def baseEnd_787781 : Nat := 359564714204166699479615

theorem tailTrace_787781 : CollatzResearch.WordTrace tailWord_787781 prefixEnd_787781 359564714204166699479615 := by
  unfold tailWord_787781
  simp only [CollatzResearch.WordTrace]
  refine ⟨28732733559011454128451197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19155155706007636085634131 28732733559011454128451197)
  ·
    refine ⟨10774775084629295298169199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28732733559011454128451197 10774775084629295298169199)
    ·
      refine ⟨16162162626943942947253799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10774775084629295298169199 16162162626943942947253799)
      ·
        refine ⟨24243243940415914420880699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16162162626943942947253799 24243243940415914420880699)
        ·
          refine ⟨36364865910623871631321049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24243243940415914420880699 36364865910623871631321049)
          ·
            refine ⟨27273649432967903723490787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36364865910623871631321049 27273649432967903723490787)
            ·
              refine ⟨40910474149451855585236181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27273649432967903723490787 40910474149451855585236181)
              ·
                refine ⟨958839237877777865278973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40910474149451855585236181 958839237877777865278973)
                ·
                  refine ⟨359564714204166699479615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958839237877777865278973 359564714204166699479615)
                  ·
                    rfl

theorem cell20_787781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_787781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787781 prefixEnd_787781 := by exact prefixLift 787781
  have htrace : WordTrace (prefixWord ++ tailWord_787781) baseStart_787781 baseEnd_787781 := by
    simpa [prefixWord, tailWord_787781, baseEnd_787781] using wordTrace_append hprefix tailTrace_787781
  have hstable : (prefixWord ++ tailWord_787781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787781).length < 2 ^ (prefixWord ++ tailWord_787781).sum := by decide
  have hdescent : baseEnd_787781 < baseStart_787781 := by decide
  rcases family_descends (prefixWord ++ tailWord_787781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787795 : List Nat := [1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_787795 : Nat := 118140960795 + 787795 * 2 ^ 59
def prefixEnd_787795 : Nat := 4983230072969 + 3 ^ 40 * 787795 * 2
def baseEnd_787795 : Nat := 119857034728548291004297

theorem tailTrace_787795 : CollatzResearch.WordTrace tailWord_787795 prefixEnd_787795 119857034728548291004297 := by
  unfold tailWord_787795
  simp only [CollatzResearch.WordTrace]
  refine ⟨28733244180960734519460839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19155496120640489679640559 28733244180960734519460839)
  ·
    refine ⟨43099866271441101779191259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28733244180960734519460839 43099866271441101779191259)
    ·
      refine ⟨64649799407161652668786889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43099866271441101779191259 64649799407161652668786889)
      ·
        refine ⟨48487349555371239501590167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64649799407161652668786889 48487349555371239501590167)
        ·
          refine ⟨72731024333056859252385251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48487349555371239501590167 72731024333056859252385251)
          ·
            refine ⟨109096536499585288878577877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72731024333056859252385251 109096536499585288878577877)
            ·
              refine ⟨2556950074209030208091669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109096536499585288878577877 2556950074209030208091669)
              ·
                refine ⟨119857034728548291004297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2556950074209030208091669 119857034728548291004297)
                ·
                  rfl

theorem cell20_787795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_787795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787795 prefixEnd_787795 := by exact prefixLift 787795
  have htrace : WordTrace (prefixWord ++ tailWord_787795) baseStart_787795 baseEnd_787795 := by
    simpa [prefixWord, tailWord_787795, baseEnd_787795] using wordTrace_append hprefix tailTrace_787795
  have hstable : (prefixWord ++ tailWord_787795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787795).length < 2 ^ (prefixWord ++ tailWord_787795).sum := by decide
  have hdescent : baseEnd_787795 < baseStart_787795 := by decide
  rcases family_descends (prefixWord ++ tailWord_787795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787812 : List Nat := [2, 3, 1, 1, 3, 4, 6]
def baseStart_787812 : Nat := 118140960795 + 787812 * 2 ^ 59
def prefixEnd_787812 : Nat := 4983230072969 + 3 ^ 40 * 787812 * 2
def baseEnd_787812 : Nat := 39953207049874263271795

theorem tailTrace_787812 : CollatzResearch.WordTrace tailWord_787812 prefixEnd_787812 39953207049874263271795 := by
  unfold tailWord_787812
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366932110949573211414845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19155909481266097615219793 14366932110949573211414845)
  ·
    refine ⟨5387599541606089954280567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14366932110949573211414845 5387599541606089954280567)
    ·
      refine ⟨8081399312409134931420851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5387599541606089954280567 8081399312409134931420851)
      ·
        refine ⟨12122098968613702397131277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8081399312409134931420851 12122098968613702397131277)
        ·
          refine ⟨4545787113230138398924229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12122098968613702397131277 4545787113230138398924229)
          ·
            refine ⟨852335083730650949798293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4545787113230138398924229 852335083730650949798293)
            ·
              refine ⟨39953207049874263271795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 852335083730650949798293 39953207049874263271795)
              ·
                rfl

theorem cell20_787812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 6].length) (baseStart_787812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787812 prefixEnd_787812 := by exact prefixLift 787812
  have htrace : WordTrace (prefixWord ++ tailWord_787812) baseStart_787812 baseEnd_787812 := by
    simpa [prefixWord, tailWord_787812, baseEnd_787812] using wordTrace_append hprefix tailTrace_787812
  have hstable : (prefixWord ++ tailWord_787812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787812).length < 2 ^ (prefixWord ++ tailWord_787812).sum := by decide
  have hdescent : baseEnd_787812 < baseStart_787812 := by decide
  rcases family_descends (prefixWord ++ tailWord_787812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787818 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_787818 : Nat := 118140960795 + 787818 * 2 ^ 59
def prefixEnd_787818 : Nat := 4983230072969 + 3 ^ 40 * 787818 * 2
def baseEnd_787818 : Nat := 359581602012359015246131

theorem tailTrace_787818 : CollatzResearch.WordTrace tailWord_787818 prefixEnd_787818 359581602012359015246131 := by
  unfold tailWord_787818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7183520764969352361887027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19156055373251606298365405 7183520764969352361887027)
  ·
    refine ⟨10775281147454028542830541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7183520764969352361887027 10775281147454028542830541)
    ·
      refine ⟨4040730430295260703561453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10775281147454028542830541 4040730430295260703561453)
      ·
        refine ⟨1515273911360722763835545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4040730430295260703561453 1515273911360722763835545)
        ·
          refine ⟨1136455433520542072876659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1515273911360722763835545 1136455433520542072876659)
          ·
            refine ⟨1704683150280813109314989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136455433520542072876659 1704683150280813109314989)
            ·
              refine ⟨639256181355304915993121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1704683150280813109314989 639256181355304915993121)
              ·
                refine ⟨479442136016478686994841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639256181355304915993121 479442136016478686994841)
                ·
                  refine ⟨359581602012359015246131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479442136016478686994841 359581602012359015246131)
                  ·
                    rfl

theorem cell20_787818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_787818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787818 prefixEnd_787818 := by exact prefixLift 787818
  have htrace : WordTrace (prefixWord ++ tailWord_787818) baseStart_787818 baseEnd_787818 := by
    simpa [prefixWord, tailWord_787818, baseEnd_787818] using wordTrace_append hprefix tailTrace_787818
  have hstable : (prefixWord ++ tailWord_787818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787818).length < 2 ^ (prefixWord ++ tailWord_787818).sum := by decide
  have hdescent : baseEnd_787818 < baseStart_787818 := by decide
  rcases family_descends (prefixWord ++ tailWord_787818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787829 : List Nat := [1, 3, 4, 1, 3, 1, 2, 5]
def baseStart_787829 : Nat := 118140960795 + 787829 * 2 ^ 59
def prefixEnd_787829 : Nat := 4983230072969 + 3 ^ 40 * 787829 * 2
def baseEnd_787829 : Nat := 119862207570697288626473

theorem tailTrace_787829 : CollatzResearch.WordTrace tailWord_787829 prefixEnd_787829 119862207570697288626473 := by
  unfold tailWord_787829
  simp only [CollatzResearch.WordTrace]
  refine ⟨28734484262837558326198541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19156322841891705550799027 28734484262837558326198541)
  ·
    refine ⟨10775431598564084372324453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28734484262837558326198541 10775431598564084372324453)
    ·
      refine ⟨2020393424730765819810835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10775431598564084372324453 2020393424730765819810835)
      ·
        refine ⟨3030590137096148729716253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020393424730765819810835 3030590137096148729716253)
        ·
          refine ⟨1136471301411055773643595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3030590137096148729716253 1136471301411055773643595)
          ·
            refine ⟨1704706952116583660465393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136471301411055773643595 1704706952116583660465393)
            ·
              refine ⟨1278530214087437745349045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704706952116583660465393 1278530214087437745349045)
              ·
                refine ⟨119862207570697288626473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1278530214087437745349045 119862207570697288626473)
                ·
                  rfl

theorem cell20_787829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_787829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787829 prefixEnd_787829 := by exact prefixLift 787829
  have htrace : WordTrace (prefixWord ++ tailWord_787829) baseStart_787829 baseEnd_787829 := by
    simpa [prefixWord, tailWord_787829, baseEnd_787829] using wordTrace_append hprefix tailTrace_787829
  have hstable : (prefixWord ++ tailWord_787829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787829).length < 2 ^ (prefixWord ++ tailWord_787829).sum := by decide
  have hdescent : baseEnd_787829 < baseStart_787829 := by decide
  rcases family_descends (prefixWord ++ tailWord_787829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787833 : List Nat := [1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_787833 : Nat := 118140960795 + 787833 * 2 ^ 59
def prefixEnd_787833 : Nat := 4983230072969 + 3 ^ 40 * 787833 * 2
def baseEnd_787833 : Nat := 119862816140361876582023

theorem tailTrace_787833 : CollatzResearch.WordTrace tailWord_787833 prefixEnd_787833 119862816140361876582023 := by
  unfold tailWord_787833
  simp only [CollatzResearch.WordTrace]
  refine ⟨28734630154823067009344153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19156420103215378006229435 28734630154823067009344153)
  ·
    refine ⟨21550972616117300257008115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28734630154823067009344153 21550972616117300257008115)
    ·
      refine ⟨32326458924175950385512173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21550972616117300257008115 32326458924175950385512173)
      ·
        refine ⟨12122422096565981394567065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32326458924175950385512173 12122422096565981394567065)
        ·
          refine ⟨9091816572424486045925299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12122422096565981394567065 9091816572424486045925299)
          ·
            refine ⟨13637724858636729068887949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9091816572424486045925299 13637724858636729068887949)
            ·
              refine ⟨5114146821988773400832981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13637724858636729068887949 5114146821988773400832981)
              ·
                refine ⟨119862816140361876582023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5114146821988773400832981 119862816140361876582023)
                ·
                  rfl

theorem cell20_787833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_787833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787833 prefixEnd_787833 := by exact prefixLift 787833
  have htrace : WordTrace (prefixWord ++ tailWord_787833) baseStart_787833 baseEnd_787833 := by
    simpa [prefixWord, tailWord_787833, baseEnd_787833] using wordTrace_append hprefix tailTrace_787833
  have hstable : (prefixWord ++ tailWord_787833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787833).length < 2 ^ (prefixWord ++ tailWord_787833).sum := by decide
  have hdescent : baseEnd_787833 < baseStart_787833 := by decide
  rcases family_descends (prefixWord ++ tailWord_787833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787870 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_787870 : Nat := 118140960795 + 787870 * 2 ^ 59
def prefixEnd_787870 : Nat := 4983230072969 + 3 ^ 40 * 787870 * 2
def baseEnd_787870 : Nat := 359605336229277945512585

theorem tailTrace_787870 : CollatzResearch.WordTrace tailWord_787870 prefixEnd_787870 359605336229277945512585 := by
  unfold tailWord_787870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591997456961127791055133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19157319770459348218960709 3591997456961127791055133)
  ·
    refine ⟨1346999046360422921645675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3591997456961127791055133 1346999046360422921645675)
    ·
      refine ⟨2020498569540634382468513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346999046360422921645675 2020498569540634382468513)
      ·
        refine ⟨1515373927155475786851385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2020498569540634382468513 1515373927155475786851385)
        ·
          refine ⟨1136530445366606840138539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1515373927155475786851385 1136530445366606840138539)
          ·
            refine ⟨1704795668049910260207809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136530445366606840138539 1704795668049910260207809)
            ·
              refine ⟨1278596751037432695155857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704795668049910260207809 1278596751037432695155857)
              ·
                refine ⟨958947563278074521366893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278596751037432695155857 958947563278074521366893)
                ·
                  refine ⟨359605336229277945512585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958947563278074521366893 359605336229277945512585)
                  ·
                    rfl

theorem cell20_787870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_787870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787870 prefixEnd_787870 := by exact prefixLift 787870
  have htrace : WordTrace (prefixWord ++ tailWord_787870) baseStart_787870 baseEnd_787870 := by
    simpa [prefixWord, tailWord_787870, baseEnd_787870] using wordTrace_append hprefix tailTrace_787870
  have hstable : (prefixWord ++ tailWord_787870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787870).length < 2 ^ (prefixWord ++ tailWord_787870).sum := by decide
  have hdescent : baseEnd_787870 < baseStart_787870 := by decide
  rcases family_descends (prefixWord ++ tailWord_787870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787871 : List Nat := [1, 1, 2, 5, 1, 10]
def baseStart_787871 : Nat := 118140960795 + 787871 * 2 ^ 59
def prefixEnd_787871 : Nat := 4983230072969 + 3 ^ 40 * 787871 * 2
def baseEnd_787871 : Nat := 13318733061352829128861

theorem tailTrace_787871 : CollatzResearch.WordTrace tailWord_787871 prefixEnd_787871 13318733061352829128861 := by
  unfold tailWord_787871
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736016128685399499227467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19157344085790266332818311 28736016128685399499227467)
  ·
    refine ⟨43104024193028099248841201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28736016128685399499227467 43104024193028099248841201)
    ·
      refine ⟨32328018144771074436630901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43104024193028099248841201 32328018144771074436630901)
      ·
        refine ⟨3030751701072288228434147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32328018144771074436630901 3030751701072288228434147)
        ·
          refine ⟨4546127551608432342651221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030751701072288228434147 4546127551608432342651221)
          ·
            refine ⟨13318733061352829128861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4546127551608432342651221 13318733061352829128861)
            ·
              rfl

theorem cell20_787871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 10].length) (baseStart_787871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787871 prefixEnd_787871 := by exact prefixLift 787871
  have htrace : WordTrace (prefixWord ++ tailWord_787871) baseStart_787871 baseEnd_787871 := by
    simpa [prefixWord, tailWord_787871, baseEnd_787871] using wordTrace_append hprefix tailTrace_787871
  have hstable : (prefixWord ++ tailWord_787871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787871).length < 2 ^ (prefixWord ++ tailWord_787871).sum := by decide
  have hdescent : baseEnd_787871 < baseStart_787871 := by decide
  rcases family_descends (prefixWord ++ tailWord_787871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787874 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_787874 : Nat := 118140960795 + 787874 * 2 ^ 59
def prefixEnd_787874 : Nat := 4983230072969 + 3 ^ 40 * 787874 * 2
def baseEnd_787874 : Nat := 359607161938271709379235

theorem tailTrace_787874 : CollatzResearch.WordTrace tailWord_787874 prefixEnd_787874 359607161938271709379235 := by
  unfold tailWord_787874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184031386918632752896669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19157417031783020674391117 7184031386918632752896669)
  ·
    refine ⟨2694011770094487282336251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7184031386918632752896669 2694011770094487282336251)
    ·
      refine ⟨4041017655141730923504377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694011770094487282336251 4041017655141730923504377)
      ·
        refine ⟨3030763241356298192628283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4041017655141730923504377 3030763241356298192628283)
        ·
          refine ⟨4546144862034447288942425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030763241356298192628283 4546144862034447288942425)
          ·
            refine ⟨3409608646525835466706819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4546144862034447288942425 3409608646525835466706819)
            ·
              refine ⟨5114412969788753200060229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409608646525835466706819 5114412969788753200060229)
              ·
                refine ⟨958952431835391225011293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5114412969788753200060229 958952431835391225011293)
                ·
                  refine ⟨359607161938271709379235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958952431835391225011293 359607161938271709379235)
                  ·
                    rfl

theorem cell20_787874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_787874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787874 prefixEnd_787874 := by exact prefixLift 787874
  have htrace : WordTrace (prefixWord ++ tailWord_787874) baseStart_787874 baseEnd_787874 := by
    simpa [prefixWord, tailWord_787874, baseEnd_787874] using wordTrace_append hprefix tailTrace_787874
  have hstable : (prefixWord ++ tailWord_787874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787874).length < 2 ^ (prefixWord ++ tailWord_787874).sum := by decide
  have hdescent : baseEnd_787874 < baseStart_787874 := by decide
  rcases family_descends (prefixWord ++ tailWord_787874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787895 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_787895 : Nat := 118140960795 + 787895 * 2 ^ 59
def prefixEnd_787895 : Nat := 4983230072969 + 3 ^ 40 * 787895 * 2
def baseEnd_787895 : Nat := 359616746910488969679149

theorem tailTrace_787895 : CollatzResearch.WordTrace tailWord_787895 prefixEnd_787895 359616746910488969679149 := by
  unfold tailWord_787895
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736891480598451598101139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19157927653732301065400759 28736891480598451598101139)
  ·
    refine ⟨43105337220897677397151709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28736891480598451598101139 43105337220897677397151709)
    ·
      refine ⟨16164501457836629023931891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43105337220897677397151709 16164501457836629023931891)
      ·
        refine ⟨24246752186754943535897837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16164501457836629023931891 24246752186754943535897837)
        ·
          refine ⟨9092532070033103825961689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24246752186754943535897837 9092532070033103825961689)
          ·
            refine ⟨6819399052524827869471267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9092532070033103825961689 6819399052524827869471267)
            ·
              refine ⟨10229098578787241804206901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819399052524827869471267 10229098578787241804206901)
              ·
                refine ⟨958977991761303919144397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10229098578787241804206901 958977991761303919144397)
                ·
                  refine ⟨359616746910488969679149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958977991761303919144397 359616746910488969679149)
                  ·
                    rfl

theorem cell20_787895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_787895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787895 prefixEnd_787895 := by exact prefixLift 787895
  have htrace : WordTrace (prefixWord ++ tailWord_787895) baseStart_787895 baseEnd_787895 := by
    simpa [prefixWord, tailWord_787895, baseEnd_787895] using wordTrace_append hprefix tailTrace_787895
  have hstable : (prefixWord ++ tailWord_787895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787895).length < 2 ^ (prefixWord ++ tailWord_787895).sum := by decide
  have hdescent : baseEnd_787895 < baseStart_787895 := by decide
  rcases family_descends (prefixWord ++ tailWord_787895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787919 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 2]
def baseStart_787919 : Nat := 118140960795 + 787919 * 2 ^ 59
def prefixEnd_787919 : Nat := 4983230072969 + 3 ^ 40 * 787919 * 2
def baseEnd_787919 : Nat := 359627701164451552879051

theorem tailTrace_787919 : CollatzResearch.WordTrace tailWord_787919 prefixEnd_787919 359627701164451552879051 := by
  unfold tailWord_787919
  simp only [CollatzResearch.WordTrace]
  refine ⟨28737766832511503696974811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19158511221674335797983207 28737766832511503696974811)
  ·
    refine ⟨43106650248767255545462217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28737766832511503696974811 43106650248767255545462217)
    ·
      refine ⟨32329987686575441659096663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43106650248767255545462217 32329987686575441659096663)
      ·
        refine ⟨48494981529863162488644995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32329987686575441659096663 48494981529863162488644995)
        ·
          refine ⟨72742472294794743732967493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48494981529863162488644995 72742472294794743732967493)
          ·
            refine ⟨13639213555274014449931405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72742472294794743732967493 13639213555274014449931405)
            ·
              refine ⟨5114705083227755418724277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13639213555274014449931405 5114705083227755418724277)
              ·
                refine ⟨479503601552602070505401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5114705083227755418724277 479503601552602070505401)
                ·
                  refine ⟨359627701164451552879051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479503601552602070505401 359627701164451552879051)
                  ·
                    rfl

theorem cell20_787919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 2].length) (baseStart_787919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787919 prefixEnd_787919 := by exact prefixLift 787919
  have htrace : WordTrace (prefixWord ++ tailWord_787919) baseStart_787919 baseEnd_787919 := by
    simpa [prefixWord, tailWord_787919, baseEnd_787919] using wordTrace_append hprefix tailTrace_787919
  have hstable : (prefixWord ++ tailWord_787919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787919).length < 2 ^ (prefixWord ++ tailWord_787919).sum := by decide
  have hdescent : baseEnd_787919 < baseStart_787919 := by decide
  rcases family_descends (prefixWord ++ tailWord_787919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787964 : List Nat := [2, 2, 2, 1, 2, 1, 6, 4]
def baseStart_787964 : Nat := 118140960795 + 787964 * 2 ^ 59
def prefixEnd_787964 : Nat := 4983230072969 + 3 ^ 40 * 787964 * 2
def baseEnd_787964 : Nat := 119882746796877132126289

theorem tailTrace_787964 : CollatzResearch.WordTrace tailWord_787964 prefixEnd_787964 119882746796877132126289 := by
  unfold tailWord_787964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14369704058674238191181473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19159605411565650921575297 14369704058674238191181473)
  ·
    refine ⟨10777278044005678643386105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14369704058674238191181473 10777278044005678643386105)
    ·
      refine ⟨8082958533004258982539579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10777278044005678643386105 8082958533004258982539579)
      ·
        refine ⟨12124437799506388473809369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082958533004258982539579 12124437799506388473809369)
        ·
          refine ⟨9093328349629791355357027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12124437799506388473809369 9093328349629791355357027)
          ·
            refine ⟨13639992524444687033035541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9093328349629791355357027 13639992524444687033035541)
            ·
              refine ⟨639374649583344704673541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13639992524444687033035541 639374649583344704673541)
              ·
                refine ⟨119882746796877132126289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639374649583344704673541 119882746796877132126289)
                ·
                  rfl

theorem cell20_787964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_787964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787964 prefixEnd_787964 := by exact prefixLift 787964
  have htrace : WordTrace (prefixWord ++ tailWord_787964) baseStart_787964 baseEnd_787964 := by
    simpa [prefixWord, tailWord_787964, baseEnd_787964] using wordTrace_append hprefix tailTrace_787964
  have hstable : (prefixWord ++ tailWord_787964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787964).length < 2 ^ (prefixWord ++ tailWord_787964).sum := by decide
  have hdescent : baseEnd_787964 < baseStart_787964 := by decide
  rcases family_descends (prefixWord ++ tailWord_787964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787970 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_787970 : Nat := 118140960795 + 787970 * 2 ^ 59
def prefixEnd_787970 : Nat := 4983230072969 + 3 ^ 40 * 787970 * 2
def baseEnd_787970 : Nat := 359650978954122042178843

theorem tailTrace_787970 : CollatzResearch.WordTrace tailWord_787970 prefixEnd_787970 359650978954122042178843 := by
  unfold tailWord_787970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184906738831684851770341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19159751303551159604720909 7184906738831684851770341)
  ·
    refine ⟨1347170013530940909706939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7184906738831684851770341 1347170013530940909706939)
    ·
      refine ⟨2020755020296411364560409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347170013530940909706939 2020755020296411364560409)
      ·
        refine ⟨1515566265222308523420307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2020755020296411364560409 1515566265222308523420307)
        ·
          refine ⟨2273349397833462785130461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515566265222308523420307 2273349397833462785130461)
          ·
            refine ⟨852506024187548544423923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2273349397833462785130461 852506024187548544423923)
            ·
              refine ⟨1278759036281322816635885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852506024187548544423923 1278759036281322816635885)
              ·
                refine ⟨479534638605496056238457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278759036281322816635885 479534638605496056238457)
                ·
                  refine ⟨359650978954122042178843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479534638605496056238457 359650978954122042178843)
                  ·
                    rfl

theorem cell20_787970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_787970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_787970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_787970 prefixEnd_787970 := by exact prefixLift 787970
  have htrace : WordTrace (prefixWord ++ tailWord_787970) baseStart_787970 baseEnd_787970 := by
    simpa [prefixWord, tailWord_787970, baseEnd_787970] using wordTrace_append hprefix tailTrace_787970
  have hstable : (prefixWord ++ tailWord_787970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787970).length < 2 ^ (prefixWord ++ tailWord_787970).sum := by decide
  have hdescent : baseEnd_787970 < baseStart_787970 := by decide
  rcases family_descends (prefixWord ++ tailWord_787970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788023 : List Nat := [1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_788023 : Nat := 118140960795 + 788023 * 2 ^ 59
def prefixEnd_788023 : Nat := 4983230072969 + 3 ^ 40 * 788023 * 2
def baseEnd_788023 : Nat := 119891723199429804470653

theorem tailTrace_788023 : CollatzResearch.WordTrace tailWord_788023 prefixEnd_788023 119891723199429804470653 := by
  unfold tailWord_788023
  simp only [CollatzResearch.WordTrace]
  refine ⟨28741560024134729458760723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19161040016089819639173815 28741560024134729458760723)
  ·
    refine ⟨43112340036202094188141085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28741560024134729458760723 43112340036202094188141085)
    ·
      refine ⟨16167127513575785320552907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43112340036202094188141085 16167127513575785320552907)
      ·
        refine ⟨24250691270363677980829361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167127513575785320552907 24250691270363677980829361)
        ·
          refine ⟨18188018452772758485622021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24250691270363677980829361 18188018452772758485622021)
          ·
            refine ⟨3410253459894892216054129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18188018452772758485622021 3410253459894892216054129)
            ·
              refine ⟨2557690094921169162040597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410253459894892216054129 2557690094921169162040597)
              ·
                refine ⟨119891723199429804470653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2557690094921169162040597 119891723199429804470653)
                ·
                  rfl

theorem cell20_788023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_788023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788023 prefixEnd_788023 := by exact prefixLift 788023
  have htrace : WordTrace (prefixWord ++ tailWord_788023) baseStart_788023 baseEnd_788023 := by
    simpa [prefixWord, tailWord_788023, baseEnd_788023] using wordTrace_append hprefix tailTrace_788023
  have hstable : (prefixWord ++ tailWord_788023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788023).length < 2 ^ (prefixWord ++ tailWord_788023).sum := by decide
  have hdescent : baseEnd_788023 < baseStart_788023 := by decide
  rcases family_descends (prefixWord ++ tailWord_788023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788050 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_788050 : Nat := 118140960795 + 788050 * 2 ^ 59
def prefixEnd_788050 : Nat := 4983230072969 + 3 ^ 40 * 788050 * 2
def baseEnd_788050 : Nat := 359687493133997319511849

theorem tailTrace_788050 : CollatzResearch.WordTrace tailWord_788050 prefixEnd_788050 359687493133997319511849 := by
  unfold tailWord_788050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185636198759228267498401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19161696530024608713329069 7185636198759228267498401)
  ·
    refine ⟨5389227149069421200623801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7185636198759228267498401 5389227149069421200623801)
    ·
      refine ⟨4041920361802065900467851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5389227149069421200623801 4041920361802065900467851)
      ·
        refine ⟨6062880542703098850701777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041920361802065900467851 6062880542703098850701777)
        ·
          refine ⟨4547160407027324138026333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6062880542703098850701777 4547160407027324138026333)
          ·
            refine ⟨1705185152635246551759875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4547160407027324138026333 1705185152635246551759875)
            ·
              refine ⟨2557777728952869827639813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705185152635246551759875 2557777728952869827639813)
              ·
                refine ⟨479583324178663092682465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2557777728952869827639813 479583324178663092682465)
                ·
                  refine ⟨359687493133997319511849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479583324178663092682465 359687493133997319511849)
                  ·
                    rfl

theorem cell20_788050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_788050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788050 prefixEnd_788050 := by exact prefixLift 788050
  have htrace : WordTrace (prefixWord ++ tailWord_788050) baseStart_788050 baseEnd_788050 := by
    simpa [prefixWord, tailWord_788050, baseEnd_788050] using wordTrace_append hprefix tailTrace_788050
  have hstable : (prefixWord ++ tailWord_788050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788050).length < 2 ^ (prefixWord ++ tailWord_788050).sum := by decide
  have hdescent : baseEnd_788050 < baseStart_788050 := by decide
  rcases family_descends (prefixWord ++ tailWord_788050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788144 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_788144 : Nat := 118140960795 + 788144 * 2 ^ 59
def prefixEnd_788144 : Nat := 4983230072969 + 3 ^ 40 * 788144 * 2
def baseEnd_788144 : Nat := 359730397295350770378131

theorem tailTrace_788144 : CollatzResearch.WordTrace tailWord_788144 prefixEnd_788144 359730397295350770378131 := by
  unfold tailWord_788144
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372986628348183561957743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19163982171130911415943657 14372986628348183561957743)
  ·
    refine ⟨21559479942522275342936615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14372986628348183561957743 21559479942522275342936615)
    ·
      refine ⟨32339219913783413014404923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21559479942522275342936615 32339219913783413014404923)
      ·
        refine ⟨48508829870675119521607385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32339219913783413014404923 48508829870675119521607385)
        ·
          refine ⟨36381622403006339641205539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48508829870675119521607385 36381622403006339641205539)
          ·
            refine ⟨54572433604509509461808309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36381622403006339641205539 54572433604509509461808309)
            ·
              refine ⟨5116165650422766512044529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54572433604509509461808309 5116165650422766512044529)
              ·
                refine ⟨3837124237817074884033397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116165650422766512044529 3837124237817074884033397)
                ·
                  refine ⟨359730397295350770378131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3837124237817074884033397 359730397295350770378131)
                  ·
                    rfl

theorem cell20_788144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_788144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788144 prefixEnd_788144 := by exact prefixLift 788144
  have htrace : WordTrace (prefixWord ++ tailWord_788144) baseStart_788144 baseEnd_788144 := by
    simpa [prefixWord, tailWord_788144, baseEnd_788144] using wordTrace_append hprefix tailTrace_788144
  have hstable : (prefixWord ++ tailWord_788144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788144).length < 2 ^ (prefixWord ++ tailWord_788144).sum := by decide
  have hdescent : baseEnd_788144 < baseStart_788144 := by decide
  rcases family_descends (prefixWord ++ tailWord_788144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788178 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_788178 : Nat := 118140960795 + 788178 * 2 ^ 59
def prefixEnd_788178 : Nat := 4983230072969 + 3 ^ 40 * 788178 * 2
def baseEnd_788178 : Nat := 359745915821797763244659

theorem tailTrace_788178 : CollatzResearch.WordTrace tailWord_788178 prefixEnd_788178 359745915821797763244659 := by
  unfold tailWord_788178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186803334643297732663297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19164808892382127287102125 7186803334643297732663297)
  ·
    refine ⟨5390102500982473299497473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7186803334643297732663297 5390102500982473299497473)
    ·
      refine ⟨4042576875736854974623105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5390102500982473299497473 4042576875736854974623105)
      ·
        refine ⟨3031932656802641230967329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4042576875736854974623105 3031932656802641230967329)
        ·
          refine ⟨2273949492601980923225497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031932656802641230967329 2273949492601980923225497)
          ·
            refine ⟨1705462119451485692419123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273949492601980923225497 1705462119451485692419123)
            ·
              refine ⟨2558193179177228538628685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705462119451485692419123 2558193179177228538628685)
              ·
                refine ⟨959322442191460701985757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2558193179177228538628685 959322442191460701985757)
                ·
                  refine ⟨359745915821797763244659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959322442191460701985757 359745915821797763244659)
                  ·
                    rfl

theorem cell20_788178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_788178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788178 prefixEnd_788178 := by exact prefixLift 788178
  have htrace : WordTrace (prefixWord ++ tailWord_788178) baseStart_788178 baseEnd_788178 := by
    simpa [prefixWord, tailWord_788178, baseEnd_788178] using wordTrace_append hprefix tailTrace_788178
  have hstable : (prefixWord ++ tailWord_788178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788178).length < 2 ^ (prefixWord ++ tailWord_788178).sum := by decide
  have hdescent : baseEnd_788178 < baseStart_788178 := by decide
  rcases family_descends (prefixWord ++ tailWord_788178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788212 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_788212 : Nat := 118140960795 + 788212 * 2 ^ 59
def prefixEnd_788212 : Nat := 4983230072969 + 3 ^ 40 * 788212 * 2
def baseEnd_788212 : Nat := 359761434348244756111187

theorem tailTrace_788212 : CollatzResearch.WordTrace tailWord_788212 prefixEnd_788212 359761434348244756111187 := by
  unfold tailWord_788212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374226710225007368695445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19165635613633343158260593 14374226710225007368695445)
  ·
    refine ⟨673791877041797220407599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14374226710225007368695445 673791877041797220407599)
    ·
      refine ⟨1010687815562695830611399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673791877041797220407599 1010687815562695830611399)
      ·
        refine ⟨1516031723344043745917099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010687815562695830611399 1516031723344043745917099)
        ·
          refine ⟨2274047585016065618875649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516031723344043745917099 2274047585016065618875649)
          ·
            refine ⟨1705535688762049214156737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274047585016065618875649 1705535688762049214156737)
            ·
              refine ⟨1279151766571536910617553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705535688762049214156737 1279151766571536910617553)
              ·
                refine ⟨959363824928652682963165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279151766571536910617553 959363824928652682963165)
                ·
                  refine ⟨359761434348244756111187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959363824928652682963165 359761434348244756111187)
                  ·
                    rfl

theorem cell20_788212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_788212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788212 prefixEnd_788212 := by exact prefixLift 788212
  have htrace : WordTrace (prefixWord ++ tailWord_788212) baseStart_788212 baseEnd_788212 := by
    simpa [prefixWord, tailWord_788212, baseEnd_788212] using wordTrace_append hprefix tailTrace_788212
  have hstable : (prefixWord ++ tailWord_788212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788212).length < 2 ^ (prefixWord ++ tailWord_788212).sum := by decide
  have hdescent : baseEnd_788212 < baseStart_788212 := by decide
  rcases family_descends (prefixWord ++ tailWord_788212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788261 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 2]
def baseStart_788261 : Nat := 118140960795 + 788261 * 2 ^ 59
def prefixEnd_788261 : Nat := 4983230072969 + 3 ^ 40 * 788261 * 2
def baseEnd_788261 : Nat := 359783799283418363477653

theorem tailTrace_788261 : CollatzResearch.WordTrace tailWord_788261 prefixEnd_788261 359783799283418363477653 := by
  unfold tailWord_788261
  simp only [CollatzResearch.WordTrace]
  refine ⟨28750240597272496105924637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19166827064848330737283091 28750240597272496105924637)
  ·
    refine ⟨10781340223977186039721739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28750240597272496105924637 10781340223977186039721739)
    ·
      refine ⟨16172010335965779059582609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781340223977186039721739 16172010335965779059582609)
      ·
        refine ⟨12129007751974334294686957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16172010335965779059582609 12129007751974334294686957)
        ·
          refine ⟨4548377906990375360507609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12129007751974334294686957 4548377906990375360507609)
          ·
            refine ⟨3411283430242781520380707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4548377906990375360507609 3411283430242781520380707)
            ·
              refine ⟨5116925145364172280571061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411283430242781520380707 5116925145364172280571061)
              ·
                refine ⟨479711732377891151303537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5116925145364172280571061 479711732377891151303537)
                ·
                  refine ⟨359783799283418363477653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479711732377891151303537 359783799283418363477653)
                  ·
                    rfl

theorem cell20_788261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_788261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788261 prefixEnd_788261 := by exact prefixLift 788261
  have htrace : WordTrace (prefixWord ++ tailWord_788261) baseStart_788261 baseEnd_788261 := by
    simpa [prefixWord, tailWord_788261, baseEnd_788261] using wordTrace_append hprefix tailTrace_788261
  have hstable : (prefixWord ++ tailWord_788261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788261).length < 2 ^ (prefixWord ++ tailWord_788261).sum := by decide
  have hdescent : baseEnd_788261 < baseStart_788261 := by decide
  rcases family_descends (prefixWord ++ tailWord_788261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788275 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_788275 : Nat := 118140960795 + 788275 * 2 ^ 59
def prefixEnd_788275 : Nat := 4983230072969 + 3 ^ 40 * 788275 * 2
def baseEnd_788275 : Nat := 359790189264896537010929

theorem tailTrace_788275 : CollatzResearch.WordTrace tailWord_788275 prefixEnd_788275 359790189264896537010929 := by
  unfold tailWord_788275
  simp only [CollatzResearch.WordTrace]
  refine ⟨28750751219221776496934279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19167167479481184331289519 28750751219221776496934279)
  ·
    refine ⟨43126126828832664745401419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28750751219221776496934279 43126126828832664745401419)
    ·
      refine ⟨64689190243248997118102129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43126126828832664745401419 64689190243248997118102129)
      ·
        refine ⟨48516892682436747838576597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64689190243248997118102129 48516892682436747838576597)
        ·
          refine ⟨1137114672244611277466639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48516892682436747838576597 1137114672244611277466639)
          ·
            refine ⟨1705672008366916916199959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137114672244611277466639 1705672008366916916199959)
            ·
              refine ⟨2558508012550375374299939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705672008366916916199959 2558508012550375374299939)
              ·
                refine ⟨3837762018825563061449909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558508012550375374299939 3837762018825563061449909)
                ·
                  refine ⟨359790189264896537010929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3837762018825563061449909 359790189264896537010929)
                  ·
                    rfl

theorem cell20_788275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_788275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788275 prefixEnd_788275 := by exact prefixLift 788275
  have htrace : WordTrace (prefixWord ++ tailWord_788275) baseStart_788275 baseEnd_788275 := by
    simpa [prefixWord, tailWord_788275, baseEnd_788275] using wordTrace_append hprefix tailTrace_788275
  have hstable : (prefixWord ++ tailWord_788275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788275).length < 2 ^ (prefixWord ++ tailWord_788275).sum := by decide
  have hdescent : baseEnd_788275 < baseStart_788275 := by decide
  rcases family_descends (prefixWord ++ tailWord_788275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788278 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_788278 : Nat := 118140960795 + 788278 * 2 ^ 59
def prefixEnd_788278 : Nat := 4983230072969 + 3 ^ 40 * 788278 * 2
def baseEnd_788278 : Nat := 359791558546641859910917

theorem tailTrace_788278 : CollatzResearch.WordTrace tailWord_788278 prefixEnd_788278 359791558546641859910917 := by
  unfold tailWord_788278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796928789888181750580843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19167240425473938672862325 1796928789888181750580843)
  ·
    refine ⟨2695393184832272625871265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796928789888181750580843 2695393184832272625871265)
    ·
      refine ⟨2021544888624204469403449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695393184832272625871265 2021544888624204469403449)
      ·
        refine ⟨1516158666468153352052587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021544888624204469403449 1516158666468153352052587)
        ·
          refine ⟨2274237999702230028078881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516158666468153352052587 2274237999702230028078881)
          ·
            refine ⟨1705678499776672521059161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274237999702230028078881 1705678499776672521059161)
            ·
              refine ⟨1279258874832504390794371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705678499776672521059161 1279258874832504390794371)
              ·
                refine ⟨1918888312248756586191557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279258874832504390794371 1918888312248756586191557)
                ·
                  refine ⟨359791558546641859910917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918888312248756586191557 359791558546641859910917)
                  ·
                    rfl

theorem cell20_788278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_788278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788278 prefixEnd_788278 := by exact prefixLift 788278
  have htrace : WordTrace (prefixWord ++ tailWord_788278) baseStart_788278 baseEnd_788278 := by
    simpa [prefixWord, tailWord_788278, baseEnd_788278] using wordTrace_append hprefix tailTrace_788278
  have hstable : (prefixWord ++ tailWord_788278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788278).length < 2 ^ (prefixWord ++ tailWord_788278).sum := by decide
  have hdescent : baseEnd_788278 < baseStart_788278 := by decide
  rcases family_descends (prefixWord ++ tailWord_788278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788282 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_788282 : Nat := 118140960795 + 788282 * 2 ^ 59
def prefixEnd_788282 : Nat := 4983230072969 + 3 ^ 40 * 788282 * 2
def baseEnd_788282 : Nat := 359793384255635623777567

theorem tailTrace_788282 : CollatzResearch.WordTrace tailWord_788282 prefixEnd_788282 359793384255635623777567 := by
  unfold tailWord_788282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187751632549104173109775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19167337686797611128292733 7187751632549104173109775)
  ·
    refine ⟨10781627448823656259664663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7187751632549104173109775 10781627448823656259664663)
    ·
      refine ⟨16172441173235484389496995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781627448823656259664663 16172441173235484389496995)
      ·
        refine ⟨24258661759853226584245493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16172441173235484389496995 24258661759853226584245493)
        ·
          refine ⟨2274249539986239992273015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24258661759853226584245493 2274249539986239992273015)
          ·
            refine ⟨3411374309979359988409523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274249539986239992273015 3411374309979359988409523)
            ·
              refine ⟨5117061464969039982614285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411374309979359988409523 5117061464969039982614285)
              ·
                refine ⟨1918898049363389993480357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5117061464969039982614285 1918898049363389993480357)
                ·
                  refine ⟨359793384255635623777567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918898049363389993480357 359793384255635623777567)
                  ·
                    rfl

theorem cell20_788282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_788282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788282 prefixEnd_788282 := by exact prefixLift 788282
  have htrace : WordTrace (prefixWord ++ tailWord_788282) baseStart_788282 baseEnd_788282 := by
    simpa [prefixWord, tailWord_788282, baseEnd_788282] using wordTrace_append hprefix tailTrace_788282
  have hstable : (prefixWord ++ tailWord_788282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788282).length < 2 ^ (prefixWord ++ tailWord_788282).sum := by decide
  have hdescent : baseEnd_788282 < baseStart_788282 := by decide
  rcases family_descends (prefixWord ++ tailWord_788282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788306 : List Nat := [3, 2, 2, 1, 1, 3, 4, 4]
def baseStart_788306 : Nat := 118140960795 + 788306 * 2 ^ 59
def prefixEnd_788306 : Nat := 4983230072969 + 3 ^ 40 * 788306 * 2
def baseEnd_788306 : Nat := 119934779503199402325823

theorem tailTrace_788306 : CollatzResearch.WordTrace tailWord_788306 prefixEnd_788306 119934779503199402325823 := by
  unfold tailWord_788306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187970470527367197828193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19167921254739645860875181 7187970470527367197828193)
  ·
    refine ⟨5390977852895525398371145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7187970470527367197828193 5390977852895525398371145)
    ·
      refine ⟨4043233389671644048778359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5390977852895525398371145 4043233389671644048778359)
      ·
        refine ⟨6064850084507466073167539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043233389671644048778359 6064850084507466073167539)
        ·
          refine ⟨9097275126761199109751309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064850084507466073167539 9097275126761199109751309)
          ·
            refine ⟨3411478172535449666156741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9097275126761199109751309 3411478172535449666156741)
            ·
              refine ⟨639652157350396812404389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3411478172535449666156741 639652157350396812404389)
              ·
                refine ⟨119934779503199402325823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639652157350396812404389 119934779503199402325823)
                ·
                  rfl

theorem cell20_788306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_788306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788306 prefixEnd_788306 := by exact prefixLift 788306
  have htrace : WordTrace (prefixWord ++ tailWord_788306) baseStart_788306 baseEnd_788306 := by
    simpa [prefixWord, tailWord_788306, baseEnd_788306] using wordTrace_append hprefix tailTrace_788306
  have hstable : (prefixWord ++ tailWord_788306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788306).length < 2 ^ (prefixWord ++ tailWord_788306).sum := by decide
  have hdescent : baseEnd_788306 < baseStart_788306 := by decide
  rcases family_descends (prefixWord ++ tailWord_788306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788382 : List Nat := [4, 3, 1, 3, 9]
def baseStart_788382 : Nat := 118140960795 + 788382 * 2 ^ 59
def prefixEnd_788382 : Nat := 4983230072969 + 3 ^ 40 * 788382 * 2
def baseEnd_788382 : Nat := 4442457123215799017825

theorem tailTrace_788382 : CollatzResearch.WordTrace tailWord_788382 prefixEnd_788382 4442457123215799017825 := by
  unfold tailWord_788382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3594331728729266721384925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19169769219889422514052933 3594331728729266721384925)
  ·
    refine ⟨1347874398273475020519347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3594331728729266721384925 1347874398273475020519347)
    ·
      refine ⟨2021811597410212530779021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347874398273475020519347 2021811597410212530779021)
      ·
        refine ⟨758179349028829699042133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2021811597410212530779021 758179349028829699042133)
        ·
          refine ⟨4442457123215799017825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 758179349028829699042133 4442457123215799017825)
          ·
            rfl

theorem cell20_788382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 9].length) (baseStart_788382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788382 prefixEnd_788382 := by exact prefixLift 788382
  have htrace : WordTrace (prefixWord ++ tailWord_788382) baseStart_788382 baseEnd_788382 := by
    simpa [prefixWord, tailWord_788382, baseEnd_788382] using wordTrace_append hprefix tailTrace_788382
  have hstable : (prefixWord ++ tailWord_788382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788382).length < 2 ^ (prefixWord ++ tailWord_788382).sum := by decide
  have hdescent : baseEnd_788382 < baseStart_788382 := by decide
  rcases family_descends (prefixWord ++ tailWord_788382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788441 : List Nat := [1, 2, 1, 2, 6, 1, 7]
def baseStart_788441 : Nat := 118140960795 + 788441 * 2 ^ 59
def prefixEnd_788441 : Nat := 4983230072969 + 3 ^ 40 * 788441 * 2
def baseEnd_788441 : Nat := 39985106243126415275213

theorem tailTrace_788441 : CollatzResearch.WordTrace tailWord_788441 prefixEnd_788441 39985106243126415275213 := by
  unfold tailWord_788441
  simp only [CollatzResearch.WordTrace]
  refine ⟨28756805736620386847477177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19171203824413591231651451 28756805736620386847477177)
  ·
    refine ⟨21567604302465290135607883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28756805736620386847477177 21567604302465290135607883)
    ·
      refine ⟨32351406453697935203411825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21567604302465290135607883 32351406453697935203411825)
      ·
        refine ⟨24263554840273451402558869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32351406453697935203411825 24263554840273451402558869)
        ·
          refine ⟨1137354133137818034494947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24263554840273451402558869 1137354133137818034494947)
          ·
            refine ⟨1706031199706727051742421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137354133137818034494947 1706031199706727051742421)
            ·
              refine ⟨39985106243126415275213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1706031199706727051742421 39985106243126415275213)
              ·
                rfl

theorem cell20_788441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_788441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788441 prefixEnd_788441 := by exact prefixLift 788441
  have htrace : WordTrace (prefixWord ++ tailWord_788441) baseStart_788441 baseEnd_788441 := by
    simpa [prefixWord, tailWord_788441, baseEnd_788441] using wordTrace_append hprefix tailTrace_788441
  have hstable : (prefixWord ++ tailWord_788441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788441).length < 2 ^ (prefixWord ++ tailWord_788441).sum := by decide
  have hdescent : baseEnd_788441 < baseStart_788441 := by decide
  rcases family_descends (prefixWord ++ tailWord_788441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788451 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 2]
def baseStart_788451 : Nat := 118140960795 + 788451 * 2 ^ 59
def prefixEnd_788451 : Nat := 4983230072969 + 3 ^ 40 * 788451 * 2
def baseEnd_788451 : Nat := 359870520460622147143543

theorem tailTrace_788451 : CollatzResearch.WordTrace tailWord_788451 prefixEnd_788451 359870520460622147143543 := by
  unfold tailWord_788451
  simp only [CollatzResearch.WordTrace]
  refine ⟨28757170466584158555341207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19171446977722772370227471 28757170466584158555341207)
  ·
    refine ⟨43135755699876237833011811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28757170466584158555341207 43135755699876237833011811)
    ·
      refine ⟨64703633549814356749517717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43135755699876237833011811 64703633549814356749517717)
      ·
        refine ⟨3032982822647547972633643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64703633549814356749517717 3032982822647547972633643)
        ·
          refine ⟨4549474233971321958950465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032982822647547972633643 4549474233971321958950465)
          ·
            refine ⟨3412105675478491469212849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4549474233971321958950465 3412105675478491469212849)
            ·
              refine ⟨2559079256608868601909637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3412105675478491469212849 2559079256608868601909637)
              ·
                refine ⟨479827360614162862858057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2559079256608868601909637 479827360614162862858057)
                ·
                  refine ⟨359870520460622147143543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479827360614162862858057 359870520460622147143543)
                  ·
                    rfl

theorem cell20_788451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 2].length) (baseStart_788451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788451 prefixEnd_788451 := by exact prefixLift 788451
  have htrace : WordTrace (prefixWord ++ tailWord_788451) baseStart_788451 baseEnd_788451 := by
    simpa [prefixWord, tailWord_788451, baseEnd_788451] using wordTrace_append hprefix tailTrace_788451
  have hstable : (prefixWord ++ tailWord_788451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788451).length < 2 ^ (prefixWord ++ tailWord_788451).sum := by decide
  have hdescent : baseEnd_788451 < baseStart_788451 := by decide
  rcases family_descends (prefixWord ++ tailWord_788451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788506 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_788506 : Nat := 118140960795 + 788506 * 2 ^ 59
def prefixEnd_788506 : Nat := 4983230072969 + 3 ^ 40 * 788506 * 2
def baseEnd_788506 : Nat := 359895623959286400309985

theorem tailTrace_788506 : CollatzResearch.WordTrace tailWord_788506 prefixEnd_788506 359895623959286400309985 := by
  unfold tailWord_788506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189794120346225737148343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19172784320923268632395581 7189794120346225737148343)
  ·
    refine ⟨10784691180519338605722515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7189794120346225737148343 10784691180519338605722515)
    ·
      refine ⟨16177036770779007908583773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10784691180519338605722515 16177036770779007908583773)
      ·
        refine ⟨6066388789042127965718915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16177036770779007908583773 6066388789042127965718915)
        ·
          refine ⟨9099583183563191948578373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6066388789042127965718915 9099583183563191948578373)
          ·
            refine ⟨1706171846918098490358445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9099583183563191948578373 1706171846918098490358445)
            ·
              refine ⟨639814442594286933884417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1706171846918098490358445 639814442594286933884417)
              ·
                refine ⟨479860831945715200413313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639814442594286933884417 479860831945715200413313)
                ·
                  refine ⟨359895623959286400309985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479860831945715200413313 359895623959286400309985)
                  ·
                    rfl

theorem cell20_788506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_788506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788506 prefixEnd_788506 := by exact prefixLift 788506
  have htrace : WordTrace (prefixWord ++ tailWord_788506) baseStart_788506 baseEnd_788506 := by
    simpa [prefixWord, tailWord_788506, baseEnd_788506] using wordTrace_append hprefix tailTrace_788506
  have hstable : (prefixWord ++ tailWord_788506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788506).length < 2 ^ (prefixWord ++ tailWord_788506).sum := by decide
  have hdescent : baseEnd_788506 < baseStart_788506 := by decide
  rcases family_descends (prefixWord ++ tailWord_788506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788516 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 3]
def baseStart_788516 : Nat := 118140960795 + 788516 * 2 ^ 59
def prefixEnd_788516 : Nat := 4983230072969 + 3 ^ 40 * 788516 * 2
def baseEnd_788516 : Nat := 359900188231770809976611

theorem tailTrace_788516 : CollatzResearch.WordTrace tailWord_788516 prefixEnd_788516 359900188231770809976611 := by
  unfold tailWord_788516
  simp only [CollatzResearch.WordTrace]
  refine ⟨14379770605674337328228701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19173027474232449770971601 14379770605674337328228701)
  ·
    refine ⟨5392413977127876498085763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14379770605674337328228701 5392413977127876498085763)
    ·
      refine ⟨8088620965691814747128645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5392413977127876498085763 8088620965691814747128645)
      ·
        refine ⟨1516616431067215265086621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8088620965691814747128645 1516616431067215265086621)
        ·
          refine ⟨568731161650205724407483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1516616431067215265086621 568731161650205724407483)
          ·
            refine ⟨853096742475308586611225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568731161650205724407483 853096742475308586611225)
            ·
              refine ⟨639822556856481439958419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853096742475308586611225 639822556856481439958419)
              ·
                refine ⟨959733835284722159937629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639822556856481439958419 959733835284722159937629)
                ·
                  refine ⟨359900188231770809976611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959733835284722159937629 359900188231770809976611)
                  ·
                    rfl

theorem cell20_788516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_788516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788516 prefixEnd_788516 := by exact prefixLift 788516
  have htrace : WordTrace (prefixWord ++ tailWord_788516) baseStart_788516 baseEnd_788516 := by
    simpa [prefixWord, tailWord_788516, baseEnd_788516] using wordTrace_append hprefix tailTrace_788516
  have hstable : (prefixWord ++ tailWord_788516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788516).length < 2 ^ (prefixWord ++ tailWord_788516).sum := by decide
  have hdescent : baseEnd_788516 < baseStart_788516 := by decide
  rcases family_descends (prefixWord ++ tailWord_788516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788517 : List Nat := [1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_788517 : Nat := 118140960795 + 788517 * 2 ^ 59
def prefixEnd_788517 : Nat := 4983230072969 + 3 ^ 40 * 788517 * 2
def baseEnd_788517 : Nat := 119966881553006416981091

theorem tailTrace_788517 : CollatzResearch.WordTrace tailWord_788517 prefixEnd_788517 119966881553006416981091 := by
  unfold tailWord_788517
  simp only [CollatzResearch.WordTrace]
  refine ⟨28759577684345051827243805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19173051789563367884829203 28759577684345051827243805)
  ·
    refine ⟨10784841631629394435216427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28759577684345051827243805 10784841631629394435216427)
    ·
      refine ⟨16177262447444091652824641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10784841631629394435216427 16177262447444091652824641)
      ·
        refine ⟨12132946835583068739618481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16177262447444091652824641 12132946835583068739618481)
        ·
          refine ⟨9099710126687301554713861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12132946835583068739618481 9099710126687301554713861)
          ·
            refine ⟨1706195648753869041508849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9099710126687301554713861 1706195648753869041508849)
            ·
              refine ⟨1279646736565401781131637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706195648753869041508849 1279646736565401781131637)
              ·
                refine ⟨119966881553006416981091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1279646736565401781131637 119966881553006416981091)
                ·
                  rfl

theorem cell20_788517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_788517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788517 prefixEnd_788517 := by exact prefixLift 788517
  have htrace : WordTrace (prefixWord ++ tailWord_788517) baseStart_788517 baseEnd_788517 := by
    simpa [prefixWord, tailWord_788517, baseEnd_788517] using wordTrace_append hprefix tailTrace_788517
  have hstable : (prefixWord ++ tailWord_788517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788517).length < 2 ^ (prefixWord ++ tailWord_788517).sum := by decide
  have hdescent : baseEnd_788517 < baseStart_788517 := by decide
  rcases family_descends (prefixWord ++ tailWord_788517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788531 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_788531 : Nat := 118140960795 + 788531 * 2 ^ 59
def prefixEnd_788531 : Nat := 4983230072969 + 3 ^ 40 * 788531 * 2
def baseEnd_788531 : Nat := 359907034640497424476549

theorem tailTrace_788531 : CollatzResearch.WordTrace tailWord_788531 prefixEnd_788531 359907034640497424476549 := by
  unfold tailWord_788531
  simp only [CollatzResearch.WordTrace]
  refine ⟨28760088306294332218253447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19173392204196221478835631 28760088306294332218253447)
  ·
    refine ⟨43140132459441498327380171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28760088306294332218253447 43140132459441498327380171)
    ·
      refine ⟨64710198689162247491070257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43140132459441498327380171 64710198689162247491070257)
      ·
        refine ⟨48532649016871685618302693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64710198689162247491070257 48532649016871685618302693)
        ·
          refine ⟨9099871690663441053431755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48532649016871685618302693 9099871690663441053431755)
          ·
            refine ⟨13649807535995161580147633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099871690663441053431755 13649807535995161580147633)
            ·
              refine ⟨10237355651996371185110725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13649807535995161580147633 10237355651996371185110725)
              ·
                refine ⟨1919504184749319597208261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10237355651996371185110725 1919504184749319597208261)
                ·
                  refine ⟨359907034640497424476549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919504184749319597208261 359907034640497424476549)
                  ·
                    rfl

theorem cell20_788531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_788531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788531 prefixEnd_788531 := by exact prefixLift 788531
  have htrace : WordTrace (prefixWord ++ tailWord_788531) baseStart_788531 baseEnd_788531 := by
    simpa [prefixWord, tailWord_788531, baseEnd_788531] using wordTrace_append hprefix tailTrace_788531
  have hstable : (prefixWord ++ tailWord_788531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788531).length < 2 ^ (prefixWord ++ tailWord_788531).sum := by decide
  have hdescent : baseEnd_788531 < baseStart_788531 := by decide
  rcases family_descends (prefixWord ++ tailWord_788531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788565 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 2]
def baseStart_788565 : Nat := 118140960795 + 788565 * 2 ^ 59
def prefixEnd_788565 : Nat := 4983230072969 + 3 ^ 40 * 788565 * 2
def baseEnd_788565 : Nat := 359922553166944417343077

theorem tailTrace_788565 : CollatzResearch.WordTrace tailWord_788565 prefixEnd_788565 359922553166944417343077 := by
  unfold tailWord_788565
  simp only [CollatzResearch.WordTrace]
  refine ⟨28761328388171156024991149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19174218925447437349994099 28761328388171156024991149)
  ·
    refine ⟨10785498145564183509371681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28761328388171156024991149 10785498145564183509371681)
    ·
      refine ⟨8089123609173137632028761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10785498145564183509371681 8089123609173137632028761)
      ·
        refine ⟨6066842706879853224021571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8089123609173137632028761 6066842706879853224021571)
        ·
          refine ⟨9100264060319779836032357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6066842706879853224021571 9100264060319779836032357)
          ·
            refine ⟨1706299511309958719256067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9100264060319779836032357 1706299511309958719256067)
            ·
              refine ⟨2559449266964938078884101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706299511309958719256067 2559449266964938078884101)
              ·
                refine ⟨479896737555925889790769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2559449266964938078884101 479896737555925889790769)
                ·
                  refine ⟨359922553166944417343077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479896737555925889790769 359922553166944417343077)
                  ·
                    rfl

theorem cell20_788565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_788565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788565 prefixEnd_788565 := by exact prefixLift 788565
  have htrace : WordTrace (prefixWord ++ tailWord_788565) baseStart_788565 baseEnd_788565 := by
    simpa [prefixWord, tailWord_788565, baseEnd_788565] using wordTrace_append hprefix tailTrace_788565
  have hstable : (prefixWord ++ tailWord_788565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788565).length < 2 ^ (prefixWord ++ tailWord_788565).sum := by decide
  have hdescent : baseEnd_788565 < baseStart_788565 := by decide
  rcases family_descends (prefixWord ++ tailWord_788565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788569 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_788569 : Nat := 118140960795 + 788569 * 2 ^ 59
def prefixEnd_788569 : Nat := 4983230072969 + 3 ^ 40 * 788569 * 2
def baseEnd_788569 : Nat := 359924378875938181209727

theorem tailTrace_788569 : CollatzResearch.WordTrace tailWord_788569 prefixEnd_788569 359924378875938181209727 := by
  unfold tailWord_788569
  simp only [CollatzResearch.WordTrace]
  refine ⟨28761474280156664708136761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19174316186771109805424507 28761474280156664708136761)
  ·
    refine ⟨21571105710117498531102571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28761474280156664708136761 21571105710117498531102571)
    ·
      refine ⟨32356658565176247796653857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21571105710117498531102571 32356658565176247796653857)
      ·
        refine ⟨24267493923882185847490393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32356658565176247796653857 24267493923882185847490393)
        ·
          refine ⟨18200620442911639385617795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24267493923882185847490393 18200620442911639385617795)
          ·
            refine ⟨27300930664367459078426693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18200620442911639385617795 27300930664367459078426693)
            ·
              refine ⟨5118924499568898577205005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27300930664367459078426693 5118924499568898577205005)
              ·
                refine ⟨1919596687338336966451877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5118924499568898577205005 1919596687338336966451877)
                ·
                  refine ⟨359924378875938181209727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919596687338336966451877 359924378875938181209727)
                  ·
                    rfl

theorem cell20_788569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_788569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788569 prefixEnd_788569 := by exact prefixLift 788569
  have htrace : WordTrace (prefixWord ++ tailWord_788569) baseStart_788569 baseEnd_788569 := by
    simpa [prefixWord, tailWord_788569, baseEnd_788569] using wordTrace_append hprefix tailTrace_788569
  have hstable : (prefixWord ++ tailWord_788569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788569).length < 2 ^ (prefixWord ++ tailWord_788569).sum := by decide
  have hdescent : baseEnd_788569 < baseStart_788569 := by decide
  rcases family_descends (prefixWord ++ tailWord_788569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788572 : List Nat := [2, 2, 4, 1, 1, 4, 1, 5]
def baseStart_788572 : Nat := 118140960795 + 788572 * 2 ^ 59
def prefixEnd_788572 : Nat := 4983230072969 + 3 ^ 40 * 788572 * 2
def baseEnd_788572 : Nat := 119975249385894501369905

theorem tailTrace_788572 : CollatzResearch.WordTrace tailWord_788572 prefixEnd_788572 119975249385894501369905 := by
  unfold tailWord_788572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380791849572898110247985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19174389132763864146997313 14380791849572898110247985)
  ·
    refine ⟨10785593887179673582685989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14380791849572898110247985 10785593887179673582685989)
    ·
      refine ⟨2022298853846188796753623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10785593887179673582685989 2022298853846188796753623)
      ·
        refine ⟨3033448280769283195130435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022298853846188796753623 3033448280769283195130435)
        ·
          refine ⟨4550172421153924792695653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033448280769283195130435 4550172421153924792695653)
          ·
            refine ⟨853157328966360898630435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4550172421153924792695653 853157328966360898630435)
            ·
              refine ⟨1279735993449541347945653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853157328966360898630435 1279735993449541347945653)
              ·
                refine ⟨119975249385894501369905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1279735993449541347945653 119975249385894501369905)
                ·
                  rfl

theorem cell20_788572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_788572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788572 prefixEnd_788572 := by exact prefixLift 788572
  have htrace : WordTrace (prefixWord ++ tailWord_788572) baseStart_788572 baseEnd_788572 := by
    simpa [prefixWord, tailWord_788572, baseEnd_788572] using wordTrace_append hprefix tailTrace_788572
  have hstable : (prefixWord ++ tailWord_788572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788572).length < 2 ^ (prefixWord ++ tailWord_788572).sum := by decide
  have hdescent : baseEnd_788572 < baseStart_788572 := by decide
  rcases family_descends (prefixWord ++ tailWord_788572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788593 : List Nat := [1, 2, 2, 2, 1, 1, 7, 4]
def baseStart_788593 : Nat := 118140960795 + 788593 * 2 ^ 59
def prefixEnd_788593 : Nat := 4983230072969 + 3 ^ 40 * 788593 * 2
def baseEnd_788593 : Nat := 119978444376633588136543

theorem tailTrace_788593 : CollatzResearch.WordTrace tailWord_788593 prefixEnd_788593 119978444376633588136543 := by
  unfold tailWord_788593
  simp only [CollatzResearch.WordTrace]
  refine ⟨28762349632069716807010433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19174899754713144538006955 28762349632069716807010433)
  ·
    refine ⟨21571762224052287605257825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28762349632069716807010433 21571762224052287605257825)
    ·
      refine ⟨16178821668039215703943369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21571762224052287605257825 16178821668039215703943369)
      ·
        refine ⟨12134116251029411777957527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16178821668039215703943369 12134116251029411777957527)
        ·
          refine ⟨18201174376544117666936291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134116251029411777957527 18201174376544117666936291)
          ·
            refine ⟨27301761564816176500404437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18201174376544117666936291 27301761564816176500404437)
            ·
              refine ⟨639885036675379136728229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27301761564816176500404437 639885036675379136728229)
              ·
                refine ⟨119978444376633588136543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639885036675379136728229 119978444376633588136543)
                ·
                  rfl

theorem cell20_788593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_788593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788593 prefixEnd_788593 := by exact prefixLift 788593
  have htrace : WordTrace (prefixWord ++ tailWord_788593) baseStart_788593 baseEnd_788593 := by
    simpa [prefixWord, tailWord_788593, baseEnd_788593] using wordTrace_append hprefix tailTrace_788593
  have hstable : (prefixWord ++ tailWord_788593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788593).length < 2 ^ (prefixWord ++ tailWord_788593).sum := by decide
  have hdescent : baseEnd_788593 < baseStart_788593 := by decide
  rcases family_descends (prefixWord ++ tailWord_788593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788624 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 2]
def baseStart_788624 : Nat := 118140960795 + 788624 * 2 ^ 59
def prefixEnd_788624 : Nat := 4983230072969 + 3 ^ 40 * 788624 * 2
def baseEnd_788624 : Nat := 359949482374602434376169

theorem tailTrace_788624 : CollatzResearch.WordTrace tailWord_788624 prefixEnd_788624 359949482374602434376169 := by
  unfold tailWord_788624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381740147478704550694463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19175653529971606067592617 14381740147478704550694463)
  ·
    refine ⟨21572610221218056826041695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14381740147478704550694463 21572610221218056826041695)
    ·
      refine ⟨32358915331827085239062543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21572610221218056826041695 32358915331827085239062543)
      ·
        refine ⟨48538372997740627858593815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32358915331827085239062543 48538372997740627858593815)
        ·
          refine ⟨72807559496610941787890723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48538372997740627858593815 72807559496610941787890723)
          ·
            refine ⟨109211339244916412681836085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72807559496610941787890723 109211339244916412681836085)
            ·
              refine ⟨10238563054210913688922133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109211339244916412681836085 10238563054210913688922133)
              ·
                refine ⟨479932643166136579168225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10238563054210913688922133 479932643166136579168225)
                ·
                  refine ⟨359949482374602434376169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479932643166136579168225 359949482374602434376169)
                  ·
                    rfl

theorem cell20_788624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_788624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788624 prefixEnd_788624 := by exact prefixLift 788624
  have htrace : WordTrace (prefixWord ++ tailWord_788624) baseStart_788624 baseEnd_788624 := by
    simpa [prefixWord, tailWord_788624, baseEnd_788624] using wordTrace_append hprefix tailTrace_788624
  have hstable : (prefixWord ++ tailWord_788624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788624).length < 2 ^ (prefixWord ++ tailWord_788624).sum := by decide
  have hdescent : baseEnd_788624 < baseStart_788624 := by decide
  rcases family_descends (prefixWord ++ tailWord_788624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788645 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_788645 : Nat := 118140960795 + 788645 * 2 ^ 59
def prefixEnd_788645 : Nat := 4983230072969 + 3 ^ 40 * 788645 * 2
def baseEnd_788645 : Nat := 359959067346819694676083

theorem tailTrace_788645 : CollatzResearch.WordTrace tailWord_788645 prefixEnd_788645 359959067346819694676083 := by
  unfold tailWord_788645
  simp only [CollatzResearch.WordTrace]
  refine ⟨28764246227881329687903389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19176164151920886458602259 28764246227881329687903389)
  ·
    refine ⟨10786592335455498632963771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28764246227881329687903389 10786592335455498632963771)
    ·
      refine ⟨16179888503183247949445657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786592335455498632963771 16179888503183247949445657)
      ·
        refine ⟨12134916377387435962084243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16179888503183247949445657 12134916377387435962084243)
        ·
          refine ⟨18202374566081153943126365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134916377387435962084243 18202374566081153943126365)
          ·
            refine ⟨6825890462280432728672387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18202374566081153943126365 6825890462280432728672387)
            ·
              refine ⟨10238835693420649093008581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825890462280432728672387 10238835693420649093008581)
              ·
                refine ⟨1919781692516371704939109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10238835693420649093008581 1919781692516371704939109)
                ·
                  refine ⟨359959067346819694676083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919781692516371704939109 359959067346819694676083)
                  ·
                    rfl

theorem cell20_788645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_788645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788645 prefixEnd_788645 := by exact prefixLift 788645
  have htrace : WordTrace (prefixWord ++ tailWord_788645) baseStart_788645 baseEnd_788645 := by
    simpa [prefixWord, tailWord_788645, baseEnd_788645] using wordTrace_append hprefix tailTrace_788645
  have hstable : (prefixWord ++ tailWord_788645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788645).length < 2 ^ (prefixWord ++ tailWord_788645).sum := by decide
  have hdescent : baseEnd_788645 < baseStart_788645 := by decide
  rcases family_descends (prefixWord ++ tailWord_788645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788654 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_788654 : Nat := 118140960795 + 788654 * 2 ^ 59
def prefixEnd_788654 : Nat := 4983230072969 + 3 ^ 40 * 788654 * 2
def baseEnd_788654 : Nat := 359963175192055663376047

theorem tailTrace_788654 : CollatzResearch.WordTrace tailWord_788654 prefixEnd_788654 359963175192055663376047 := by
  unfold tailWord_788654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595571810606090528122627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19176382989899149483320677 3595571810606090528122627)
  ·
    refine ⟨5393357715909135792183941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595571810606090528122627 5393357715909135792183941)
    ·
      refine ⟨1011254571732962961034489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5393357715909135792183941 1011254571732962961034489)
      ·
        refine ⟨758440928799722220775867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011254571732962961034489 758440928799722220775867)
        ·
          refine ⟨1137661393199583331163801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758440928799722220775867 1137661393199583331163801)
          ·
            refine ⟨853246044899687498372851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137661393199583331163801 853246044899687498372851)
            ·
              refine ⟨1279869067349531247559277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853246044899687498372851 1279869067349531247559277)
              ·
                refine ⟨479950900256074217834729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1279869067349531247559277 479950900256074217834729)
                ·
                  refine ⟨359963175192055663376047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479950900256074217834729 359963175192055663376047)
                  ·
                    rfl

theorem cell20_788654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_788654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788654 prefixEnd_788654 := by exact prefixLift 788654
  have htrace : WordTrace (prefixWord ++ tailWord_788654) baseStart_788654 baseEnd_788654 := by
    simpa [prefixWord, tailWord_788654, baseEnd_788654] using wordTrace_append hprefix tailTrace_788654
  have hstable : (prefixWord ++ tailWord_788654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788654).length < 2 ^ (prefixWord ++ tailWord_788654).sum := by decide
  have hdescent : baseEnd_788654 < baseStart_788654 := by decide
  rcases family_descends (prefixWord ++ tailWord_788654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788745 : List Nat := [1, 2, 1, 1, 3, 6, 1, 5]
def baseStart_788745 : Nat := 118140960795 + 788745 * 2 ^ 59
def prefixEnd_788745 : Nat := 4983230072969 + 3 ^ 40 * 788745 * 2
def baseEnd_788745 : Nat := 120001570023887930447447

theorem tailTrace_788745 : CollatzResearch.WordTrace tailWord_788745 prefixEnd_788745 120001570023887930447447 := by
  unfold tailWord_788745
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767893527519046766543689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19178595685012697844362459 28767893527519046766543689)
  ·
    refine ⟨21575920145639285074907767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28767893527519046766543689 21575920145639285074907767)
    ·
      refine ⟨32363880218458927612361651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21575920145639285074907767 32363880218458927612361651)
      ·
        refine ⟨48545820327688391418542477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32363880218458927612361651 48545820327688391418542477)
        ·
          refine ⟨18204682622883146781953429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48545820327688391418542477 18204682622883146781953429)
          ·
            refine ⟨853344497947647505404067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18204682622883146781953429 853344497947647505404067)
            ·
              refine ⟨1280016746921471258106101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853344497947647505404067 1280016746921471258106101)
              ·
                refine ⟨120001570023887930447447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1280016746921471258106101 120001570023887930447447)
                ·
                  rfl

theorem cell20_788745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_788745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788745 prefixEnd_788745 := by exact prefixLift 788745
  have htrace : WordTrace (prefixWord ++ tailWord_788745) baseStart_788745 baseEnd_788745 := by
    simpa [prefixWord, tailWord_788745, baseEnd_788745] using wordTrace_append hprefix tailTrace_788745
  have hstable : (prefixWord ++ tailWord_788745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788745).length < 2 ^ (prefixWord ++ tailWord_788745).sum := by decide
  have hdescent : baseEnd_788745 < baseStart_788745 := by decide
  rcases family_descends (prefixWord ++ tailWord_788745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788759 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_788759 : Nat := 118140960795 + 788759 * 2 ^ 59
def prefixEnd_788759 : Nat := 4983230072969 + 3 ^ 40 * 788759 * 2
def baseEnd_788759 : Nat := 360011100053141964875617

theorem tailTrace_788759 : CollatzResearch.WordTrace tailWord_788759 prefixEnd_788759 360011100053141964875617 := by
  unfold tailWord_788759
  simp only [CollatzResearch.WordTrace]
  refine ⟨28768404149468327157553331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19178936099645551438368887 28768404149468327157553331)
  ·
    refine ⟨43152606224202490736329997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28768404149468327157553331 43152606224202490736329997)
    ·
      refine ⟨16182227334075934026123749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43152606224202490736329997 16182227334075934026123749)
      ·
        refine ⟨3034167625139237629898203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16182227334075934026123749 3034167625139237629898203)
        ·
          refine ⟨4551251437708856444847305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034167625139237629898203 4551251437708856444847305)
          ·
            refine ⟨3413438578281642333635479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551251437708856444847305 3413438578281642333635479)
            ·
              refine ⟨5120157867422463500453219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413438578281642333635479 5120157867422463500453219)
              ·
                refine ⟨7680236801133695250679829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120157867422463500453219 7680236801133695250679829)
                ·
                  refine ⟨360011100053141964875617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7680236801133695250679829 360011100053141964875617)
                  ·
                    rfl

theorem cell20_788759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_788759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788759 prefixEnd_788759 := by exact prefixLift 788759
  have htrace : WordTrace (prefixWord ++ tailWord_788759) baseStart_788759 baseEnd_788759 := by
    simpa [prefixWord, tailWord_788759, baseEnd_788759] using wordTrace_append hprefix tailTrace_788759
  have hstable : (prefixWord ++ tailWord_788759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788759).length < 2 ^ (prefixWord ++ tailWord_788759).sum := by decide
  have hdescent : baseEnd_788759 < baseStart_788759 := by decide
  rcases family_descends (prefixWord ++ tailWord_788759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788762 : List Nat := [3, 1, 1, 3, 4, 1, 3, 4]
def baseStart_788762 : Nat := 118140960795 + 788762 * 2 ^ 59
def prefixEnd_788762 : Nat := 4983230072969 + 3 ^ 40 * 788762 * 2
def baseEnd_788762 : Nat := 120004156444962429258535

theorem tailTrace_788762 : CollatzResearch.WordTrace tailWord_788762 prefixEnd_788762 120004156444962429258535 := by
  unfold tailWord_788762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7192128392114364667478135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19179009045638305779941693 7192128392114364667478135)
  ·
    refine ⟨10788192588171547001217203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7192128392114364667478135 10788192588171547001217203)
    ·
      refine ⟨16182288882257320501825805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10788192588171547001217203 16182288882257320501825805)
      ·
        refine ⟨6068358330846495188184677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16182288882257320501825805 6068358330846495188184677)
        ·
          refine ⟨1137817187033717847784627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6068358330846495188184677 1137817187033717847784627)
          ·
            refine ⟨1706725780550576771676941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137817187033717847784627 1706725780550576771676941)
            ·
              refine ⟨640022167706466289378853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1706725780550576771676941 640022167706466289378853)
              ·
                refine ⟨120004156444962429258535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640022167706466289378853 120004156444962429258535)
                ·
                  rfl

theorem cell20_788762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_788762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788762 prefixEnd_788762 := by exact prefixLift 788762
  have htrace : WordTrace (prefixWord ++ tailWord_788762) baseStart_788762 baseEnd_788762 := by
    simpa [prefixWord, tailWord_788762, baseEnd_788762] using wordTrace_append hprefix tailTrace_788762
  have hstable : (prefixWord ++ tailWord_788762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788762).length < 2 ^ (prefixWord ++ tailWord_788762).sum := by decide
  have hdescent : baseEnd_788762 < baseStart_788762 := by decide
  rcases family_descends (prefixWord ++ tailWord_788762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788782 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_788782 : Nat := 118140960795 + 788782 * 2 ^ 59
def prefixEnd_788782 : Nat := 4983230072969 + 3 ^ 40 * 788782 * 2
def baseEnd_788782 : Nat := 360021597879856107108857

theorem tailTrace_788782 : CollatzResearch.WordTrace tailWord_788782 prefixEnd_788782 360021597879856107108857 := by
  unfold tailWord_788782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596155378548125260705075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19179495352256668057093733 3596155378548125260705075)
  ·
    refine ⟨5394233067822187891057613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3596155378548125260705075 5394233067822187891057613)
    ·
      refine ⟨2022837400433320459146605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5394233067822187891057613 2022837400433320459146605)
      ·
        refine ⟨758564025162495172179977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2022837400433320459146605 758564025162495172179977)
        ·
          refine ⟨568923018871871379134983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758564025162495172179977 568923018871871379134983)
          ·
            refine ⟨853384528307807068702475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568923018871871379134983 853384528307807068702475)
            ·
              refine ⟨1280076792461710603053713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853384528307807068702475 1280076792461710603053713)
              ·
                refine ⟨960057594346282952290285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280076792461710603053713 960057594346282952290285)
                ·
                  refine ⟨360021597879856107108857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960057594346282952290285 360021597879856107108857)
                  ·
                    rfl

theorem cell20_788782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_788782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788782 prefixEnd_788782 := by exact prefixLift 788782
  have htrace : WordTrace (prefixWord ++ tailWord_788782) baseStart_788782 baseEnd_788782 := by
    simpa [prefixWord, tailWord_788782, baseEnd_788782] using wordTrace_append hprefix tailTrace_788782
  have hstable : (prefixWord ++ tailWord_788782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788782).length < 2 ^ (prefixWord ++ tailWord_788782).sum := by decide
  have hdescent : baseEnd_788782 < baseStart_788782 := by decide
  rcases family_descends (prefixWord ++ tailWord_788782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788786 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_788786 : Nat := 118140960795 + 788786 * 2 ^ 59
def prefixEnd_788786 : Nat := 4983230072969 + 3 ^ 40 * 788786 * 2
def baseEnd_788786 : Nat := 360023423588849870975507

theorem tailTrace_788786 : CollatzResearch.WordTrace tailWord_788786 prefixEnd_788786 360023423588849870975507 := by
  unfold tailWord_788786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7192347230092627692196553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19179592613580340512524141 7192347230092627692196553)
  ·
    refine ⟨5394260422569470769147415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7192347230092627692196553 5394260422569470769147415)
    ·
      refine ⟨8091390633854206153721123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5394260422569470769147415 8091390633854206153721123)
      ·
        refine ⟨12137085950781309230581685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091390633854206153721123 12137085950781309230581685)
        ·
          refine ⟨1137851807885747740367033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12137085950781309230581685 1137851807885747740367033)
          ·
            refine ⟨853388855914310805275275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137851807885747740367033 853388855914310805275275)
            ·
              refine ⟨1280083283871466207912913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853388855914310805275275 1280083283871466207912913)
              ·
                refine ⟨960062462903599655934685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280083283871466207912913 960062462903599655934685)
                ·
                  refine ⟨360023423588849870975507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960062462903599655934685 360023423588849870975507)
                  ·
                    rfl

theorem cell20_788786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_788786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788786 prefixEnd_788786 := by exact prefixLift 788786
  have htrace : WordTrace (prefixWord ++ tailWord_788786) baseStart_788786 baseEnd_788786 := by
    simpa [prefixWord, tailWord_788786, baseEnd_788786] using wordTrace_append hprefix tailTrace_788786
  have hstable : (prefixWord ++ tailWord_788786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788786).length < 2 ^ (prefixWord ++ tailWord_788786).sum := by decide
  have hdescent : baseEnd_788786 < baseStart_788786 := by decide
  rcases family_descends (prefixWord ++ tailWord_788786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788793 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 2]
def baseStart_788793 : Nat := 118140960795 + 788793 * 2 ^ 59
def prefixEnd_788793 : Nat := 4983230072969 + 3 ^ 40 * 788793 * 2
def baseEnd_788793 : Nat := 360026618579588957742145

theorem tailTrace_788793 : CollatzResearch.WordTrace tailWord_788793 prefixEnd_788793 360026618579588957742145 := by
  unfold tailWord_788793
  simp only [CollatzResearch.WordTrace]
  refine ⟨28769644231345150964291033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19179762820896767309527355 28769644231345150964291033)
  ·
    refine ⟨21577233173508863223218275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28769644231345150964291033 21577233173508863223218275)
    ·
      refine ⟨32365849760263294834827413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21577233173508863223218275 32365849760263294834827413)
      ·
        refine ⟨1517149207512341945382535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32365849760263294834827413 1517149207512341945382535)
        ·
          refine ⟨2275723811268512918073803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517149207512341945382535 2275723811268512918073803)
          ·
            refine ⟨3413585716902769377110705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275723811268512918073803 3413585716902769377110705)
            ·
              refine ⟨2560189287677077032833029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413585716902769377110705 2560189287677077032833029)
              ·
                refine ⟨480035491439451943656193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2560189287677077032833029 480035491439451943656193)
                ·
                  refine ⟨360026618579588957742145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480035491439451943656193 360026618579588957742145)
                  ·
                    rfl

theorem cell20_788793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_788793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788793 prefixEnd_788793 := by exact prefixLift 788793
  have htrace : WordTrace (prefixWord ++ tailWord_788793) baseStart_788793 baseEnd_788793 := by
    simpa [prefixWord, tailWord_788793, baseEnd_788793] using wordTrace_append hprefix tailTrace_788793
  have hstable : (prefixWord ++ tailWord_788793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788793).length < 2 ^ (prefixWord ++ tailWord_788793).sum := by decide
  have hdescent : baseEnd_788793 < baseStart_788793 := by decide
  rcases family_descends (prefixWord ++ tailWord_788793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788807 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 3]
def baseStart_788807 : Nat := 118140960795 + 788807 * 2 ^ 59
def prefixEnd_788807 : Nat := 4983230072969 + 3 ^ 40 * 788807 * 2
def baseEnd_788807 : Nat := 360033008561067131275421

theorem tailTrace_788807 : CollatzResearch.WordTrace tailWord_788807 prefixEnd_788807 360033008561067131275421 := by
  unfold tailWord_788807
  simp only [CollatzResearch.WordTrace]
  refine ⟨28770154853294431355300675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19180103235529620903533783 28770154853294431355300675)
  ·
    refine ⟨43155232279941647032951013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28770154853294431355300675 43155232279941647032951013)
    ·
      refine ⟨8091606052489058818678315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43155232279941647032951013 8091606052489058818678315)
      ·
        refine ⟨12137409078733588228017473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091606052489058818678315 12137409078733588228017473)
        ·
          refine ⟨9103056809050191171013105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12137409078733588228017473 9103056809050191171013105)
          ·
            refine ⟨6827292606787643378259829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9103056809050191171013105 6827292606787643378259829)
            ·
              refine ⟨640058681886341566711859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6827292606787643378259829 640058681886341566711859)
              ·
                refine ⟨960088022829512350067789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640058681886341566711859 960088022829512350067789)
                ·
                  refine ⟨360033008561067131275421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960088022829512350067789 360033008561067131275421)
                  ·
                    rfl

theorem cell20_788807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_788807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788807 prefixEnd_788807 := by exact prefixLift 788807
  have htrace : WordTrace (prefixWord ++ tailWord_788807) baseStart_788807 baseEnd_788807 := by
    simpa [prefixWord, tailWord_788807, baseEnd_788807] using wordTrace_append hprefix tailTrace_788807
  have hstable : (prefixWord ++ tailWord_788807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788807).length < 2 ^ (prefixWord ++ tailWord_788807).sum := by decide
  have hdescent : baseEnd_788807 < baseStart_788807 := by decide
  rcases family_descends (prefixWord ++ tailWord_788807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788821 : List Nat := [1, 3, 2, 2, 4, 1, 1, 6]
def baseStart_788821 : Nat := 118140960795 + 788821 * 2 ^ 59
def prefixEnd_788821 : Nat := 4983230072969 + 3 ^ 40 * 788821 * 2
def baseEnd_788821 : Nat := 120013132847515101602899

theorem tailTrace_788821 : CollatzResearch.WordTrace tailWord_788821 prefixEnd_788821 120013132847515101602899 := by
  unfold tailWord_788821
  simp only [CollatzResearch.WordTrace]
  refine ⟨28770665475243711746310317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19180443650162474497540211 28770665475243711746310317)
  ·
    refine ⟨10788999553216391904866369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28770665475243711746310317 10788999553216391904866369)
    ·
      refine ⟨8091749664912293928649777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10788999553216391904866369 8091749664912293928649777)
      ·
        refine ⟨6068812248684220446487333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8091749664912293928649777 6068812248684220446487333)
        ·
          refine ⟨1137902296628291333716375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6068812248684220446487333 1137902296628291333716375)
          ·
            refine ⟨1706853444942437000574563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137902296628291333716375 1706853444942437000574563)
            ·
              refine ⟨2560280167413655500861845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706853444942437000574563 2560280167413655500861845)
              ·
                refine ⟨120013132847515101602899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2560280167413655500861845 120013132847515101602899)
                ·
                  rfl

theorem cell20_788821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_788821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788821 prefixEnd_788821 := by exact prefixLift 788821
  have htrace : WordTrace (prefixWord ++ tailWord_788821) baseStart_788821 baseEnd_788821 := by
    simpa [prefixWord, tailWord_788821, baseEnd_788821] using wordTrace_append hprefix tailTrace_788821
  have hstable : (prefixWord ++ tailWord_788821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788821).length < 2 ^ (prefixWord ++ tailWord_788821).sum := by decide
  have hdescent : baseEnd_788821 < baseStart_788821 := by decide
  rcases family_descends (prefixWord ++ tailWord_788821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788887 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_788887 : Nat := 118140960795 + 788887 * 2 ^ 59
def prefixEnd_788887 : Nat := 4983230072969 + 3 ^ 40 * 788887 * 2
def baseEnd_788887 : Nat := 360069522740942408608427

theorem tailTrace_788887 : CollatzResearch.WordTrace tailWord_788887 prefixEnd_788887 360069522740942408608427 := by
  unfold tailWord_788887
  simp only [CollatzResearch.WordTrace]
  refine ⟨28773072693004605018212915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19182048462003070012141943 28773072693004605018212915)
  ·
    refine ⟨43159609039506907527319373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28773072693004605018212915 43159609039506907527319373)
    ·
      refine ⟨16184853389815090322744765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43159609039506907527319373 16184853389815090322744765)
      ·
        refine ⟨6069320021180658871029287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16184853389815090322744765 6069320021180658871029287)
        ·
          refine ⟨9103980031770988306543931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6069320021180658871029287 9103980031770988306543931)
          ·
            refine ⟨13655970047656482459815897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103980031770988306543931 13655970047656482459815897)
            ·
              refine ⟨10241977535742361844861923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13655970047656482459815897 10241977535742361844861923)
              ·
                refine ⟨15362966303613542767292885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10241977535742361844861923 15362966303613542767292885)
                ·
                  refine ⟨360069522740942408608427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15362966303613542767292885 360069522740942408608427)
                  ·
                    rfl

theorem cell20_788887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_788887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788887 prefixEnd_788887 := by exact prefixLift 788887
  have htrace : WordTrace (prefixWord ++ tailWord_788887) baseStart_788887 baseEnd_788887 := by
    simpa [prefixWord, tailWord_788887, baseEnd_788887] using wordTrace_append hprefix tailTrace_788887
  have hstable : (prefixWord ++ tailWord_788887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788887).length < 2 ^ (prefixWord ++ tailWord_788887).sum := by decide
  have hdescent : baseEnd_788887 < baseStart_788887 := by decide
  rcases family_descends (prefixWord ++ tailWord_788887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788897 : List Nat := [1, 2, 3, 5, 1, 8]
def baseStart_788897 : Nat := 118140960795 + 788897 * 2 ^ 59
def prefixEnd_788897 : Nat := 4983230072969 + 3 ^ 40 * 788897 * 2
def baseEnd_788897 : Nat := 13336077296793585862039

theorem tailTrace_788897 : CollatzResearch.WordTrace tailWord_788897 prefixEnd_788897 13336077296793585862039 := by
  unfold tailWord_788897
  simp only [CollatzResearch.WordTrace]
  refine ⟨28773437422968376726076945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19182291615312251150717963 28773437422968376726076945)
  ·
    refine ⟨21580078067226282544557709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28773437422968376726076945 21580078067226282544557709)
    ·
      refine ⟨8092529275209855954209141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21580078067226282544557709 8092529275209855954209141)
      ·
        refine ⟨758674619550923995707107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8092529275209855954209141 758674619550923995707107)
        ·
          refine ⟨1138011929326385993560661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758674619550923995707107 1138011929326385993560661)
          ·
            refine ⟨13336077296793585862039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1138011929326385993560661 13336077296793585862039)
            ·
              rfl

theorem cell20_788897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 8].length) (baseStart_788897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788897 prefixEnd_788897 := by exact prefixLift 788897
  have htrace : WordTrace (prefixWord ++ tailWord_788897) baseStart_788897 baseEnd_788897 := by
    simpa [prefixWord, tailWord_788897, baseEnd_788897] using wordTrace_append hprefix tailTrace_788897
  have hstable : (prefixWord ++ tailWord_788897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788897).length < 2 ^ (prefixWord ++ tailWord_788897).sum := by decide
  have hdescent : baseEnd_788897 < baseStart_788897 := by decide
  rcases family_descends (prefixWord ++ tailWord_788897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788935 : List Nat := [1, 1, 4, 1, 1, 5, 3, 4]
def baseStart_788935 : Nat := 118140960795 + 788935 * 2 ^ 59
def prefixEnd_788935 : Nat := 4983230072969 + 3 ^ 40 * 788935 * 2
def baseEnd_788935 : Nat := 120030477082955858336077

theorem tailTrace_788935 : CollatzResearch.WordTrace tailWord_788935 prefixEnd_788935 120030477082955858336077 := by
  unfold tailWord_788935
  simp only [CollatzResearch.WordTrace]
  refine ⟨28774823396830709215960259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19183215597887139477306839 28774823396830709215960259)
  ·
    refine ⟨43162235095246063823940389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28774823396830709215960259 43162235095246063823940389)
    ·
      refine ⟨8092919080358636966988823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43162235095246063823940389 8092919080358636966988823)
      ·
        refine ⟨12139378620537955450483235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092919080358636966988823 12139378620537955450483235)
        ·
          refine ⟨18209067930806933175724853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12139378620537955450483235 18209067930806933175724853)
          ·
            refine ⟨1707100118513149985224205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18209067930806933175724853 1707100118513149985224205)
            ·
              refine ⟨640162544442431244459077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707100118513149985224205 640162544442431244459077)
              ·
                refine ⟨120030477082955858336077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640162544442431244459077 120030477082955858336077)
                ·
                  rfl

theorem cell20_788935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_788935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788935 prefixEnd_788935 := by exact prefixLift 788935
  have htrace : WordTrace (prefixWord ++ tailWord_788935) baseStart_788935 baseEnd_788935 := by
    simpa [prefixWord, tailWord_788935, baseEnd_788935] using wordTrace_append hprefix tailTrace_788935
  have hstable : (prefixWord ++ tailWord_788935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788935).length < 2 ^ (prefixWord ++ tailWord_788935).sum := by decide
  have hdescent : baseEnd_788935 < baseStart_788935 := by decide
  rcases family_descends (prefixWord ++ tailWord_788935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788959 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 3]
def baseStart_788959 : Nat := 118140960795 + 788959 * 2 ^ 59
def prefixEnd_788959 : Nat := 4983230072969 + 3 ^ 40 * 788959 * 2
def baseEnd_788959 : Nat := 360102385502830158208133

theorem tailTrace_788959 : CollatzResearch.WordTrace tailWord_788959 prefixEnd_788959 360102385502830158208133 := by
  unfold tailWord_788959
  simp only [CollatzResearch.WordTrace]
  refine ⟨28775698748743761314833931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19183799165829174209889287 28775698748743761314833931)
  ·
    refine ⟨43163548123115641972250897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28775698748743761314833931 43163548123115641972250897)
    ·
      refine ⟨32372661092336731479188173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43163548123115641972250897 32372661092336731479188173)
      ·
        refine ⟨12139747909626274304695565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32372661092336731479188173 12139747909626274304695565)
        ·
          refine ⟨4552405466109852864260837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12139747909626274304695565 4552405466109852864260837)
          ·
            refine ⟨853576024895597412048907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4552405466109852864260837 853576024895597412048907)
            ·
              refine ⟨1280364037343396118073361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853576024895597412048907 1280364037343396118073361)
              ·
                refine ⟨960273028007547088555021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280364037343396118073361 960273028007547088555021)
                ·
                  refine ⟨360102385502830158208133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960273028007547088555021 360102385502830158208133)
                  ·
                    rfl

theorem cell20_788959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_788959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788959 prefixEnd_788959 := by exact prefixLift 788959
  have htrace : WordTrace (prefixWord ++ tailWord_788959) baseStart_788959 baseEnd_788959 := by
    simpa [prefixWord, tailWord_788959, baseEnd_788959] using wordTrace_append hprefix tailTrace_788959
  have hstable : (prefixWord ++ tailWord_788959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788959).length < 2 ^ (prefixWord ++ tailWord_788959).sum := by decide
  have hdescent : baseEnd_788959 < baseStart_788959 := by decide
  rcases family_descends (prefixWord ++ tailWord_788959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788962 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_788962 : Nat := 118140960795 + 788962 * 2 ^ 59
def prefixEnd_788962 : Nat := 4983230072969 + 3 ^ 40 * 788962 * 2
def baseEnd_788962 : Nat := 360103754784575481108121

theorem tailTrace_788962 : CollatzResearch.WordTrace tailWord_788962 prefixEnd_788962 360103754784575481108121 := by
  unfold tailWord_788962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193952041933223206798285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19183872111821928551462093 7193952041933223206798285)
  ·
    refine ⟨2697732015724958702549357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7193952041933223206798285 2697732015724958702549357)
    ·
      refine ⟨1011649505896859513456009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2697732015724958702549357 1011649505896859513456009)
      ·
        refine ⟨758737129422644635092007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011649505896859513456009 758737129422644635092007)
        ·
          refine ⟨1138105694133966952638011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758737129422644635092007 1138105694133966952638011)
          ·
            refine ⟨1707158541200950428957017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138105694133966952638011 1707158541200950428957017)
            ·
              refine ⟨1280368905900712821717763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707158541200950428957017 1280368905900712821717763)
              ·
                refine ⟨1920553358851069232576645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280368905900712821717763 1920553358851069232576645)
                ·
                  refine ⟨360103754784575481108121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920553358851069232576645 360103754784575481108121)
                  ·
                    rfl

theorem cell20_788962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_788962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_788962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_788962 prefixEnd_788962 := by exact prefixLift 788962
  have htrace : WordTrace (prefixWord ++ tailWord_788962) baseStart_788962 baseEnd_788962 := by
    simpa [prefixWord, tailWord_788962, baseEnd_788962] using wordTrace_append hprefix tailTrace_788962
  have hstable : (prefixWord ++ tailWord_788962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788962).length < 2 ^ (prefixWord ++ tailWord_788962).sum := by decide
  have hdescent : baseEnd_788962 < baseStart_788962 := by decide
  rcases family_descends (prefixWord ++ tailWord_788962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789028 : List Nat := [2, 3, 1, 5, 1, 1, 2, 5]
def baseStart_789028 : Nat := 118140960795 + 789028 * 2 ^ 59
def prefixEnd_789028 : Nat := 4983230072969 + 3 ^ 40 * 789028 * 2
def baseEnd_789028 : Nat := 120044626327657528302617

theorem tailTrace_789028 : CollatzResearch.WordTrace tailWord_789028 prefixEnd_789028 120044626327657528302617 := by
  unfold tailWord_789028
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389107692746893049547869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19185476923662524066063825 14389107692746893049547869)
  ·
    refine ⟨5395915384780084893580451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14389107692746893049547869 5395915384780084893580451)
    ·
      refine ⟨8093873077170127340370677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5395915384780084893580451 8093873077170127340370677)
      ·
        refine ⟨758800600984699438159751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8093873077170127340370677 758800600984699438159751)
        ·
          refine ⟨1138200901477049157239627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758800600984699438159751 1138200901477049157239627)
          ·
            refine ⟨1707301352215573735859441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138200901477049157239627 1707301352215573735859441)
            ·
              refine ⟨1280476014161680301894581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707301352215573735859441 1280476014161680301894581)
              ·
                refine ⟨120044626327657528302617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1280476014161680301894581 120044626327657528302617)
                ·
                  rfl

theorem cell20_789028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_789028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789028 prefixEnd_789028 := by exact prefixLift 789028
  have htrace : WordTrace (prefixWord ++ tailWord_789028) baseStart_789028 baseEnd_789028 := by
    simpa [prefixWord, tailWord_789028, baseEnd_789028] using wordTrace_append hprefix tailTrace_789028
  have hstable : (prefixWord ++ tailWord_789028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789028).length < 2 ^ (prefixWord ++ tailWord_789028).sum := by decide
  have hdescent : baseEnd_789028 < baseStart_789028 := by decide
  rcases family_descends (prefixWord ++ tailWord_789028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789076 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 2]
def baseStart_789076 : Nat := 118140960795 + 789076 * 2 ^ 59
def prefixEnd_789076 : Nat := 4983230072969 + 3 ^ 40 * 789076 * 2
def baseEnd_789076 : Nat := 360155787490897751307655

theorem tailTrace_789076 : CollatzResearch.WordTrace tailWord_789076 prefixEnd_789076 360155787490897751307655 := by
  unfold tailWord_789076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389983044659945148421541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19186644059546593531228721 14389983044659945148421541)
  ·
    refine ⟨2698121820873739715329039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14389983044659945148421541 2698121820873739715329039)
    ·
      refine ⟨4047182731310609572993559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698121820873739715329039 4047182731310609572993559)
      ·
        refine ⟨6070774096965914359490339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047182731310609572993559 6070774096965914359490339)
        ·
          refine ⟨9106161145448871539235509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070774096965914359490339 9106161145448871539235509)
          ·
            refine ⟨853702607385831706803329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9106161145448871539235509 853702607385831706803329)
            ·
              refine ⟨640276955539373780102497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853702607385831706803329 640276955539373780102497)
              ·
                refine ⟨480207716654530335076873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640276955539373780102497 480207716654530335076873)
                ·
                  refine ⟨360155787490897751307655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480207716654530335076873 360155787490897751307655)
                  ·
                    rfl

theorem cell20_789076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_789076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789076 prefixEnd_789076 := by exact prefixLift 789076
  have htrace : WordTrace (prefixWord ++ tailWord_789076) baseStart_789076 baseEnd_789076 := by
    simpa [prefixWord, tailWord_789076, baseEnd_789076] using wordTrace_append hprefix tailTrace_789076
  have hstable : (prefixWord ++ tailWord_789076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789076).length < 2 ^ (prefixWord ++ tailWord_789076).sum := by decide
  have hdescent : baseEnd_789076 < baseStart_789076 := by decide
  rcases family_descends (prefixWord ++ tailWord_789076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789077 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_789077 : Nat := 118140960795 + 789077 * 2 ^ 59
def prefixEnd_789077 : Nat := 4983230072969 + 3 ^ 40 * 789077 * 2
def baseEnd_789077 : Nat := 360156243918146192274317

theorem tailTrace_789077 : CollatzResearch.WordTrace tailWord_789077 prefixEnd_789077 360156243918146192274317 := by
  unfold tailWord_789077
  simp only [CollatzResearch.WordTrace]
  refine ⟨28780002562316267467629485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19186668374877511645086323 28780002562316267467629485)
  ·
    refine ⟨10792500960868600300361057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28780002562316267467629485 10792500960868600300361057)
    ·
      refine ⟨8094375720651450225270793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10792500960868600300361057 8094375720651450225270793)
      ·
        refine ⟨6070781790488587668953095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8094375720651450225270793 6070781790488587668953095)
        ·
          refine ⟨9106172685732881503429643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070781790488587668953095 9106172685732881503429643)
          ·
            refine ⟨13659259028599322255144465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9106172685732881503429643 13659259028599322255144465)
            ·
              refine ⟨10244444271449491691358349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13659259028599322255144465 10244444271449491691358349)
              ·
                refine ⟨3841666601793559384259381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10244444271449491691358349 3841666601793559384259381)
                ·
                  refine ⟨360156243918146192274317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841666601793559384259381 360156243918146192274317)
                  ·
                    rfl

theorem cell20_789077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_789077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789077 prefixEnd_789077 := by exact prefixLift 789077
  have htrace : WordTrace (prefixWord ++ tailWord_789077) baseStart_789077 baseEnd_789077 := by
    simpa [prefixWord, tailWord_789077, baseEnd_789077] using wordTrace_append hprefix tailTrace_789077
  have hstable : (prefixWord ++ tailWord_789077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789077).length < 2 ^ (prefixWord ++ tailWord_789077).sum := by decide
  have hdescent : baseEnd_789077 < baseStart_789077 := by decide
  rcases family_descends (prefixWord ++ tailWord_789077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789101 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_789101 : Nat := 118140960795 + 789101 * 2 ^ 59
def prefixEnd_789101 : Nat := 4983230072969 + 3 ^ 40 * 789101 * 2
def baseEnd_789101 : Nat := 360167198172108775474219

theorem tailTrace_789101 : CollatzResearch.WordTrace tailWord_789101 prefixEnd_789101 360167198172108775474219 := by
  unfold tailWord_789101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28780877914229319566503157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19187251942819546377668771 28780877914229319566503157)
  ·
    refine ⟨2698207304458998709359671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28780877914229319566503157 2698207304458998709359671)
    ·
      refine ⟨4047310956688498064039507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698207304458998709359671 4047310956688498064039507)
      ·
        refine ⟨6070966435032747096059261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047310956688498064039507 6070966435032747096059261)
        ·
          refine ⟨2276612413137280161022223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6070966435032747096059261 2276612413137280161022223)
          ·
            refine ⟨3414918619705920241533335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276612413137280161022223 3414918619705920241533335)
            ·
              refine ⟨5122377929558880362300003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414918619705920241533335 5122377929558880362300003)
              ·
                refine ⟨7683566894338320543450005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122377929558880362300003 7683566894338320543450005)
                ·
                  refine ⟨360167198172108775474219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7683566894338320543450005 360167198172108775474219)
                  ·
                    rfl

theorem cell20_789101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_789101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789101 prefixEnd_789101 := by exact prefixLift 789101
  have htrace : WordTrace (prefixWord ++ tailWord_789101) baseStart_789101 baseEnd_789101 := by
    simpa [prefixWord, tailWord_789101, baseEnd_789101] using wordTrace_append hprefix tailTrace_789101
  have hstable : (prefixWord ++ tailWord_789101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789101).length < 2 ^ (prefixWord ++ tailWord_789101).sum := by decide
  have hdescent : baseEnd_789101 < baseStart_789101 := by decide
  rcases family_descends (prefixWord ++ tailWord_789101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789159 : List Nat := [1, 1, 6, 3, 1, 2, 2, 4]
def baseStart_789159 : Nat := 118140960795 + 789159 * 2 ^ 59
def prefixEnd_789159 : Nat := 4983230072969 + 3 ^ 40 * 789159 * 2
def baseEnd_789159 : Nat := 120064556984172783846883

theorem tailTrace_789159 : CollatzResearch.WordTrace tailWord_789159 prefixEnd_789159 120064556984172783846883 := by
  unfold tailWord_789159
  simp only [CollatzResearch.WordTrace]
  refine ⟨28782993348019195472114531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19188662232012796981409687 28782993348019195472114531)
  ·
    refine ⟨43174490022028793208171797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28782993348019195472114531 43174490022028793208171797)
    ·
      refine ⟨2023804219782599681633053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43174490022028793208171797 2023804219782599681633053)
      ·
        refine ⟨758926582418474880612395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2023804219782599681633053 758926582418474880612395)
        ·
          refine ⟨1138389873627712320918593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758926582418474880612395 1138389873627712320918593)
          ·
            refine ⟨853792405220784240688945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138389873627712320918593 853792405220784240688945)
            ·
              refine ⟨640344303915588180516709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853792405220784240688945 640344303915588180516709)
              ·
                refine ⟨120064556984172783846883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640344303915588180516709 120064556984172783846883)
                ·
                  rfl

theorem cell20_789159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_789159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789159 prefixEnd_789159 := by exact prefixLift 789159
  have htrace : WordTrace (prefixWord ++ tailWord_789159) baseStart_789159 baseEnd_789159 := by
    simpa [prefixWord, tailWord_789159, baseEnd_789159] using wordTrace_append hprefix tailTrace_789159
  have hstable : (prefixWord ++ tailWord_789159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789159).length < 2 ^ (prefixWord ++ tailWord_789159).sum := by decide
  have hdescent : baseEnd_789159 < baseStart_789159 := by decide
  rcases family_descends (prefixWord ++ tailWord_789159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789169 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 2]
def baseStart_789169 : Nat := 118140960795 + 789169 * 2 ^ 59
def prefixEnd_789169 : Nat := 4983230072969 + 3 ^ 40 * 789169 * 2
def baseEnd_789169 : Nat := 360198235225002761207275

theorem tailTrace_789169 : CollatzResearch.WordTrace tailWord_789169 prefixEnd_789169 360198235225002761207275 := by
  unfold tailWord_789169
  simp only [CollatzResearch.WordTrace]
  refine ⟨28783358077982967179978561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19188905385321978119985707 28783358077982967179978561)
  ·
    refine ⟨21587518558487225384983921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28783358077982967179978561 21587518558487225384983921)
    ·
      refine ⟨16190638918865419038737941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21587518558487225384983921 16190638918865419038737941)
      ·
        refine ⟨758936199321816517440841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16190638918865419038737941 758936199321816517440841)
        ·
          refine ⟨569202149491362388080631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758936199321816517440841 569202149491362388080631)
          ·
            refine ⟨853803224237043582120947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569202149491362388080631 853803224237043582120947)
            ·
              refine ⟨1280704836355565373181421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853803224237043582120947 1280704836355565373181421)
              ·
                refine ⟨480264313633337014943033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1280704836355565373181421 480264313633337014943033)
                ·
                  refine ⟨360198235225002761207275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480264313633337014943033 360198235225002761207275)
                  ·
                    rfl

theorem cell20_789169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_789169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789169 prefixEnd_789169 := by exact prefixLift 789169
  have htrace : WordTrace (prefixWord ++ tailWord_789169) baseStart_789169 baseEnd_789169 := by
    simpa [prefixWord, tailWord_789169, baseEnd_789169] using wordTrace_append hprefix tailTrace_789169
  have hstable : (prefixWord ++ tailWord_789169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789169).length < 2 ^ (prefixWord ++ tailWord_789169).sum := by decide
  have hdescent : baseEnd_789169 < baseStart_789169 := by decide
  rcases family_descends (prefixWord ++ tailWord_789169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789173 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 2]
def baseStart_789173 : Nat := 118140960795 + 789173 * 2 ^ 59
def prefixEnd_789173 : Nat := 4983230072969 + 3 ^ 40 * 789173 * 2
def baseEnd_789173 : Nat := 360200060933996525073925

theorem tailTrace_789173 : CollatzResearch.WordTrace tailWord_789173 prefixEnd_789173 360200060933996525073925 := by
  unfold tailWord_789173
  simp only [CollatzResearch.WordTrace]
  refine ⟨28783503969968475863124173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19189002646645650575416115 28783503969968475863124173)
  ·
    refine ⟨10793813988738178448671565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28783503969968475863124173 10793813988738178448671565)
    ·
      refine ⟨4047680245776816918251837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10793813988738178448671565 4047680245776816918251837)
      ·
        refine ⟨1517880092166306344344439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4047680245776816918251837 1517880092166306344344439)
        ·
          refine ⟨2276820138249459516516659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517880092166306344344439 2276820138249459516516659)
          ·
            refine ⟨3415230207374189274774989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276820138249459516516659 3415230207374189274774989)
            ·
              refine ⟨1280711327765320978040621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3415230207374189274774989 1280711327765320978040621)
              ·
                refine ⟨480266747911995366765233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1280711327765320978040621 480266747911995366765233)
                ·
                  refine ⟨360200060933996525073925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480266747911995366765233 360200060933996525073925)
                  ·
                    rfl

theorem cell20_789173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_789173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789173 prefixEnd_789173 := by exact prefixLift 789173
  have htrace : WordTrace (prefixWord ++ tailWord_789173) baseStart_789173 baseEnd_789173 := by
    simpa [prefixWord, tailWord_789173, baseEnd_789173] using wordTrace_append hprefix tailTrace_789173
  have hstable : (prefixWord ++ tailWord_789173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789173).length < 2 ^ (prefixWord ++ tailWord_789173).sum := by decide
  have hdescent : baseEnd_789173 < baseStart_789173 := by decide
  rcases family_descends (prefixWord ++ tailWord_789173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789184 : List Nat := [2, 1, 1, 2, 4, 4, 6]
def baseStart_789184 : Nat := 118140960795 + 789184 * 2 ^ 59
def prefixEnd_789184 : Nat := 4983230072969 + 3 ^ 40 * 789184 * 2
def baseEnd_789184 : Nat := 40022786848192152856357

theorem tailTrace_789184 : CollatzResearch.WordTrace tailWord_789184 prefixEnd_789184 40022786848192152856357 := by
  unfold tailWord_789184
  simp only [CollatzResearch.WordTrace]
  refine ⟨14391952586464312370887303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19189270115285749827849737 14391952586464312370887303)
  ·
    refine ⟨21587928879696468556330955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14391952586464312370887303 21587928879696468556330955)
    ·
      refine ⟨32381893319544702834496433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21587928879696468556330955 32381893319544702834496433)
      ·
        refine ⟨24286419989658527125872325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32381893319544702834496433 24286419989658527125872325)
        ·
          refine ⟨4553703748060973836101061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24286419989658527125872325 4553703748060973836101061)
          ·
            refine ⟨853819452761432594268949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4553703748060973836101061 853819452761432594268949)
            ·
              refine ⟨40022786848192152856357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 853819452761432594268949 40022786848192152856357)
              ·
                rfl

theorem cell20_789184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 6].length) (baseStart_789184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789184 prefixEnd_789184 := by exact prefixLift 789184
  have htrace : WordTrace (prefixWord ++ tailWord_789184) baseStart_789184 baseEnd_789184 := by
    simpa [prefixWord, tailWord_789184, baseEnd_789184] using wordTrace_append hprefix tailTrace_789184
  have hstable : (prefixWord ++ tailWord_789184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789184).length < 2 ^ (prefixWord ++ tailWord_789184).sum := by decide
  have hdescent : baseEnd_789184 < baseStart_789184 := by decide
  rcases family_descends (prefixWord ++ tailWord_789184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789194 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_789194 : Nat := 118140960795 + 789194 * 2 ^ 59
def prefixEnd_789194 : Nat := 4983230072969 + 3 ^ 40 * 789194 * 2
def baseEnd_789194 : Nat := 360209645906213785373839

theorem tailTrace_789194 : CollatzResearch.WordTrace tailWord_789194 prefixEnd_789194 360209645906213785373839 := by
  unfold tailWord_789194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196067475723099112409659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19189513268594930966425757 7196067475723099112409659)
  ·
    refine ⟨10794101213584648668614489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7196067475723099112409659 10794101213584648668614489)
    ·
      refine ⟨8095575910188486501460867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10794101213584648668614489 8095575910188486501460867)
      ·
        refine ⟨12143363865282729752191301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8095575910188486501460867 12143363865282729752191301)
        ·
          refine ⟨2276880724740511828535869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12143363865282729752191301 2276880724740511828535869)
          ·
            refine ⟨853830271777691935700951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2276880724740511828535869 853830271777691935700951)
            ·
              refine ⟨1280745407666537903551427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853830271777691935700951 1280745407666537903551427)
              ·
                refine ⟨1921118111499806855327141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280745407666537903551427 1921118111499806855327141)
                ·
                  refine ⟨360209645906213785373839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921118111499806855327141 360209645906213785373839)
                  ·
                    rfl

theorem cell20_789194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_789194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789194 prefixEnd_789194 := by exact prefixLift 789194
  have htrace : WordTrace (prefixWord ++ tailWord_789194) baseStart_789194 baseEnd_789194 := by
    simpa [prefixWord, tailWord_789194, baseEnd_789194] using wordTrace_append hprefix tailTrace_789194
  have hstable : (prefixWord ++ tailWord_789194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789194).length < 2 ^ (prefixWord ++ tailWord_789194).sum := by decide
  have hdescent : baseEnd_789194 < baseStart_789194 := by decide
  rcases family_descends (prefixWord ++ tailWord_789194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789208 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_789208 : Nat := 118140960795 + 789208 * 2 ^ 59
def prefixEnd_789208 : Nat := 4983230072969 + 3 ^ 40 * 789208 * 2
def baseEnd_789208 : Nat := 360216035887691958907115

theorem tailTrace_789208 : CollatzResearch.WordTrace tailWord_789208 prefixEnd_789208 360216035887691958907115 := by
  unfold tailWord_789208
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392390262420838420324139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19189853683227784560432185 14392390262420838420324139)
  ·
    refine ⟨21588585393631257630486209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14392390262420838420324139 21588585393631257630486209)
    ·
      refine ⟨16191439045223443222864657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21588585393631257630486209 16191439045223443222864657)
      ·
        refine ⟨12143579283917582417148493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16191439045223443222864657 12143579283917582417148493)
        ·
          refine ⟨4553842231469093406430685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12143579283917582417148493 4553842231469093406430685)
          ·
            refine ⟨1707690836800910027411507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4553842231469093406430685 1707690836800910027411507)
            ·
              refine ⟨2561536255201365041117261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707690836800910027411507 2561536255201365041117261)
              ·
                refine ⟨960576095700511890418973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2561536255201365041117261 960576095700511890418973)
                ·
                  refine ⟨360216035887691958907115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960576095700511890418973 360216035887691958907115)
                  ·
                    rfl

theorem cell20_789208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_789208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789208 prefixEnd_789208 := by exact prefixLift 789208
  have htrace : WordTrace (prefixWord ++ tailWord_789208) baseStart_789208 baseEnd_789208 := by
    simpa [prefixWord, tailWord_789208, baseEnd_789208] using wordTrace_append hprefix tailTrace_789208
  have hstable : (prefixWord ++ tailWord_789208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789208).length < 2 ^ (prefixWord ++ tailWord_789208).sum := by decide
  have hdescent : baseEnd_789208 < baseStart_789208 := by decide
  rcases family_descends (prefixWord ++ tailWord_789208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789267 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_789267 : Nat := 118140960795 + 789267 * 2 ^ 59
def prefixEnd_789267 : Nat := 4983230072969 + 3 ^ 40 * 789267 * 2
def baseEnd_789267 : Nat := 360242965095349975940207

theorem tailTrace_789267 : CollatzResearch.WordTrace tailWord_789267 prefixEnd_789267 360242965095349975940207 := by
  unfold tailWord_789267
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786932431627929917046055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19191288287751953278030703 28786932431627929917046055)
  ·
    refine ⟨43180398647441894875569083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28786932431627929917046055 43180398647441894875569083)
    ·
      refine ⟨64770597971162842313353625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43180398647441894875569083 64770597971162842313353625)
      ·
        refine ⟨48577948478372131735015219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64770597971162842313353625 48577948478372131735015219)
        ·
          refine ⟨72866922717558197602522829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48577948478372131735015219 72866922717558197602522829)
          ·
            refine ⟨27325096019084324100946061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72866922717558197602522829 27325096019084324100946061)
            ·
              refine ⟨10246911007156621537854773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27325096019084324100946061 10246911007156621537854773)
              ·
                refine ⟨960647906920933269173885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10246911007156621537854773 960647906920933269173885)
                ·
                  refine ⟨360242965095349975940207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960647906920933269173885 360242965095349975940207)
                  ·
                    rfl

theorem cell20_789267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_789267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789267 prefixEnd_789267 := by exact prefixLift 789267
  have htrace : WordTrace (prefixWord ++ tailWord_789267) baseStart_789267 baseEnd_789267 := by
    simpa [prefixWord, tailWord_789267, baseEnd_789267] using wordTrace_append hprefix tailTrace_789267
  have hstable : (prefixWord ++ tailWord_789267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789267).length < 2 ^ (prefixWord ++ tailWord_789267).sum := by decide
  have hdescent : baseEnd_789267 < baseStart_789267 := by decide
  rcases family_descends (prefixWord ++ tailWord_789267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789291 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 2]
def baseStart_789291 : Nat := 118140960795 + 789291 * 2 ^ 59
def prefixEnd_789291 : Nat := 4983230072969 + 3 ^ 40 * 789291 * 2
def baseEnd_789291 : Nat := 360253919349312559140109

theorem tailTrace_789291 : CollatzResearch.WordTrace tailWord_789291 prefixEnd_789291 360253919349312559140109 := by
  unfold tailWord_789291
  simp only [CollatzResearch.WordTrace]
  refine ⟨28787807783540982015919727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19191871855693988010613151 28787807783540982015919727)
  ·
    refine ⟨43181711675311473023879591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28787807783540982015919727 43181711675311473023879591)
    ·
      refine ⟨64772567512967209535819387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43181711675311473023879591 64772567512967209535819387)
      ·
        refine ⟨97158851269450814303729081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64772567512967209535819387 97158851269450814303729081)
        ·
          refine ⟨72869138452088110727796811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97158851269450814303729081 72869138452088110727796811)
          ·
            refine ⟨109303707678132166091695217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72869138452088110727796811 109303707678132166091695217)
            ·
              refine ⟨81977780758599124568771413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109303707678132166091695217 81977780758599124568771413)
              ·
                refine ⟨480338559132416745520145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 81977780758599124568771413 480338559132416745520145)
                ·
                  refine ⟨360253919349312559140109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480338559132416745520145 360253919349312559140109)
                  ·
                    rfl

theorem cell20_789291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 2].length) (baseStart_789291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789291 prefixEnd_789291 := by exact prefixLift 789291
  have htrace : WordTrace (prefixWord ++ tailWord_789291) baseStart_789291 baseEnd_789291 := by
    simpa [prefixWord, tailWord_789291, baseEnd_789291] using wordTrace_append hprefix tailTrace_789291
  have hstable : (prefixWord ++ tailWord_789291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789291).length < 2 ^ (prefixWord ++ tailWord_789291).sum := by decide
  have hdescent : baseEnd_789291 < baseStart_789291 := by decide
  rcases family_descends (prefixWord ++ tailWord_789291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789301 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 3]
def baseStart_789301 : Nat := 118140960795 + 789301 * 2 ^ 59
def prefixEnd_789301 : Nat := 4983230072969 + 3 ^ 40 * 789301 * 2
def baseEnd_789301 : Nat := 360258483621796968806735

theorem tailTrace_789301 : CollatzResearch.WordTrace tailWord_789301 prefixEnd_789301 360258483621796968806735 := by
  unfold tailWord_789301
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788172513504753723783757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19192115009003169149189171 28788172513504753723783757)
  ·
    refine ⟨10795564692564282646418909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28788172513504753723783757 10795564692564282646418909)
    ·
      refine ⟨4048336759711605992407091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10795564692564282646418909 4048336759711605992407091)
      ·
        refine ⟨6072505139567408988610637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048336759711605992407091 6072505139567408988610637)
        ·
          refine ⟨2277189427337778370728989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6072505139567408988610637 2277189427337778370728989)
          ·
            refine ⟨853946035251666889023371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2277189427337778370728989 853946035251666889023371)
            ·
              refine ⟨1280919052877500333535057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853946035251666889023371 1280919052877500333535057)
              ·
                refine ⟨960689289658125250151293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280919052877500333535057 960689289658125250151293)
                ·
                  refine ⟨360258483621796968806735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960689289658125250151293 360258483621796968806735)
                  ·
                    rfl

theorem cell20_789301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_789301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789301 prefixEnd_789301 := by exact prefixLift 789301
  have htrace : WordTrace (prefixWord ++ tailWord_789301) baseStart_789301 baseEnd_789301 := by
    simpa [prefixWord, tailWord_789301, baseEnd_789301] using wordTrace_append hprefix tailTrace_789301
  have hstable : (prefixWord ++ tailWord_789301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789301).length < 2 ^ (prefixWord ++ tailWord_789301).sum := by decide
  have hdescent : baseEnd_789301 < baseStart_789301 := by decide
  rcases family_descends (prefixWord ++ tailWord_789301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789319 : List Nat := [1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_789319 : Nat := 118140960795 + 789319 * 2 ^ 59
def prefixEnd_789319 : Nat := 4983230072969 + 3 ^ 40 * 789319 * 2
def baseEnd_789319 : Nat := 120088899770756302068887

theorem tailTrace_789319 : CollatzResearch.WordTrace tailWord_789319 prefixEnd_789319 120088899770756302068887 := by
  unfold tailWord_789319
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788829027439542797939011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19192552684959695198626007 28788829027439542797939011)
  ·
    refine ⟨43183243541159314196908517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28788829027439542797939011 43183243541159314196908517)
    ·
      refine ⟨8096858163967371411920347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43183243541159314196908517 8096858163967371411920347)
      ·
        refine ⟨12145287245951057117880521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096858163967371411920347 12145287245951057117880521)
        ·
          refine ⟨9108965434463292838410391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12145287245951057117880521 9108965434463292838410391)
          ·
            refine ⟨13663448151694939257615587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108965434463292838410391 13663448151694939257615587)
            ·
              refine ⟨20495172227542408886423381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13663448151694939257615587 20495172227542408886423381)
              ·
                refine ⟨120088899770756302068887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20495172227542408886423381 120088899770756302068887)
                ·
                  rfl

theorem cell20_789319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_789319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789319 prefixEnd_789319 := by exact prefixLift 789319
  have htrace : WordTrace (prefixWord ++ tailWord_789319) baseStart_789319 baseEnd_789319 := by
    simpa [prefixWord, tailWord_789319, baseEnd_789319] using wordTrace_append hprefix tailTrace_789319
  have hstable : (prefixWord ++ tailWord_789319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789319).length < 2 ^ (prefixWord ++ tailWord_789319).sum := by decide
  have hdescent : baseEnd_789319 < baseStart_789319 := by decide
  rcases family_descends (prefixWord ++ tailWord_789319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789332 : List Nat := [2, 4, 1, 1, 4, 2, 2, 4]
def baseStart_789332 : Nat := 118140960795 + 789332 * 2 ^ 59
def prefixEnd_789332 : Nat := 4983230072969 + 3 ^ 40 * 789332 * 2
def baseEnd_789332 : Nat := 120090877622166212924425

theorem tailTrace_789332 : CollatzResearch.WordTrace tailWord_789332 prefixEnd_789332 120090877622166212924425 := by
  unfold tailWord_789332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394651588196223009081125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19192868784261630678774833 14394651588196223009081125)
  ·
    refine ⟨2698997172786791814202711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14394651588196223009081125 2698997172786791814202711)
    ·
      refine ⟨4048495759180187721304067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698997172786791814202711 4048495759180187721304067)
      ·
        refine ⟨6072743638770281581956101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048495759180187721304067 6072743638770281581956101)
        ·
          refine ⟨1138639432269427796616769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6072743638770281581956101 1138639432269427796616769)
          ·
            refine ⟨853979574202070847462577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138639432269427796616769 853979574202070847462577)
            ·
              refine ⟨640484680651553135596933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853979574202070847462577 640484680651553135596933)
              ·
                refine ⟨120090877622166212924425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640484680651553135596933 120090877622166212924425)
                ·
                  rfl

theorem cell20_789332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_789332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789332 prefixEnd_789332 := by exact prefixLift 789332
  have htrace : WordTrace (prefixWord ++ tailWord_789332) baseStart_789332 baseEnd_789332 := by
    simpa [prefixWord, tailWord_789332, baseEnd_789332] using wordTrace_append hprefix tailTrace_789332
  have hstable : (prefixWord ++ tailWord_789332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789332).length < 2 ^ (prefixWord ++ tailWord_789332).sum := by decide
  have hdescent : baseEnd_789332 < baseStart_789332 := by decide
  rcases family_descends (prefixWord ++ tailWord_789332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789367 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 2]
def baseStart_789367 : Nat := 118140960795 + 789367 * 2 ^ 59
def prefixEnd_789367 : Nat := 4983230072969 + 3 ^ 40 * 789367 * 2
def baseEnd_789367 : Nat := 360288607820194072606465

theorem tailTrace_789367 : CollatzResearch.WordTrace tailWord_789367 prefixEnd_789367 360288607820194072606465 := by
  unfold tailWord_789367
  simp only [CollatzResearch.WordTrace]
  refine ⟨28790579731265646995686355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19193719820843764663790903 28790579731265646995686355)
  ·
    refine ⟨43185869596898470493529533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28790579731265646995686355 43185869596898470493529533)
    ·
      refine ⟨16194701098836926435073575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43185869596898470493529533 16194701098836926435073575)
      ·
        refine ⟨24292051648255389652610363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16194701098836926435073575 24292051648255389652610363)
        ·
          refine ⟨36438077472383084478915545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24292051648255389652610363 36438077472383084478915545)
          ·
            refine ⟨27328558104287313359186659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36438077472383084478915545 27328558104287313359186659)
            ·
              refine ⟨40992837156430970038779989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27328558104287313359186659 40992837156430970038779989)
              ·
                refine ⟨480384810426925430141953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 40992837156430970038779989 480384810426925430141953)
                ·
                  refine ⟨360288607820194072606465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480384810426925430141953 360288607820194072606465)
                  ·
                    rfl

theorem cell20_789367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 2].length) (baseStart_789367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789367 prefixEnd_789367 := by exact prefixLift 789367
  have htrace : WordTrace (prefixWord ++ tailWord_789367) baseStart_789367 baseEnd_789367 := by
    simpa [prefixWord, tailWord_789367, baseEnd_789367] using wordTrace_append hprefix tailTrace_789367
  have hstable : (prefixWord ++ tailWord_789367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789367).length < 2 ^ (prefixWord ++ tailWord_789367).sum := by decide
  have hdescent : baseEnd_789367 < baseStart_789367 := by decide
  rcases family_descends (prefixWord ++ tailWord_789367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789388 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_789388 : Nat := 118140960795 + 789388 * 2 ^ 59
def prefixEnd_789388 : Nat := 4983230072969 + 3 ^ 40 * 789388 * 2
def baseEnd_789388 : Nat := 360298192792411332906379

theorem tailTrace_789388 : CollatzResearch.WordTrace tailWord_789388 prefixEnd_789388 360298192792411332906379 := by
  unfold tailWord_789388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14395672832094783791100409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19194230442793045054800545 14395672832094783791100409)
  ·
    refine ⟨10796754624071087843325307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14395672832094783791100409 10796754624071087843325307)
    ·
      refine ⟨16195131936106631764987961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10796754624071087843325307 16195131936106631764987961)
      ·
        refine ⟨12146348952079973823740971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16195131936106631764987961 12146348952079973823740971)
        ·
          refine ⟨18219523428119960735611457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12146348952079973823740971 18219523428119960735611457)
          ·
            refine ⟨13664642571089970551708593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18219523428119960735611457 13664642571089970551708593)
            ·
              refine ⟨10248481928317477913781445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13664642571089970551708593 10248481928317477913781445)
              ·
                refine ⟨1921590361559527108834021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10248481928317477913781445 1921590361559527108834021)
                ·
                  refine ⟨360298192792411332906379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921590361559527108834021 360298192792411332906379)
                  ·
                    rfl

theorem cell20_789388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_789388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789388 prefixEnd_789388 := by exact prefixLift 789388
  have htrace : WordTrace (prefixWord ++ tailWord_789388) baseStart_789388 baseEnd_789388 := by
    simpa [prefixWord, tailWord_789388, baseEnd_789388] using wordTrace_append hprefix tailTrace_789388
  have hstable : (prefixWord ++ tailWord_789388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789388).length < 2 ^ (prefixWord ++ tailWord_789388).sum := by decide
  have hdescent : baseEnd_789388 < baseStart_789388 := by decide
  rcases family_descends (prefixWord ++ tailWord_789388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789415 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_789415 : Nat := 118140960795 + 789415 * 2 ^ 59
def prefixEnd_789415 : Nat := 4983230072969 + 3 ^ 40 * 789415 * 2
def baseEnd_789415 : Nat := 360310516328119239006269

theorem tailTrace_789415 : CollatzResearch.WordTrace tailWord_789415 prefixEnd_789415 360310516328119239006269 := by
  unfold tailWord_789415
  simp only [CollatzResearch.WordTrace]
  refine ⟨28792330435091751193433699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19194886956727834128955799 28792330435091751193433699)
  ·
    refine ⟨43188495652637626790150549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28792330435091751193433699 43188495652637626790150549)
    ·
      refine ⟨2024460733717388755788307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43188495652637626790150549 2024460733717388755788307)
      ·
        refine ⟨3036691100576083133682461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024460733717388755788307 3036691100576083133682461)
        ·
          refine ⟨1138759162716031175130923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3036691100576083133682461 1138759162716031175130923)
          ·
            refine ⟨1708138744074046762696385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138759162716031175130923 1708138744074046762696385)
            ·
              refine ⟨1281104058055535072022289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708138744074046762696385 1281104058055535072022289)
              ·
                refine ⟨960828043541651304016717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281104058055535072022289 960828043541651304016717)
                ·
                  refine ⟨360310516328119239006269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960828043541651304016717 360310516328119239006269)
                  ·
                    rfl

theorem cell20_789415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_789415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789415 prefixEnd_789415 := by exact prefixLift 789415
  have htrace : WordTrace (prefixWord ++ tailWord_789415) baseStart_789415 baseEnd_789415 := by
    simpa [prefixWord, tailWord_789415, baseEnd_789415] using wordTrace_append hprefix tailTrace_789415
  have hstable : (prefixWord ++ tailWord_789415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789415).length < 2 ^ (prefixWord ++ tailWord_789415).sum := by decide
  have hdescent : baseEnd_789415 < baseStart_789415 := by decide
  rcases family_descends (prefixWord ++ tailWord_789415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789460 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 2]
def baseStart_789460 : Nat := 118140960795 + 789460 * 2 ^ 59
def prefixEnd_789460 : Nat := 4983230072969 + 3 ^ 40 * 789460 * 2
def baseEnd_789460 : Nat := 360331055554299082506085

theorem tailTrace_789460 : CollatzResearch.WordTrace tailWord_789460 prefixEnd_789460 360331055554299082506085 := by
  unfold tailWord_789460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14396985859964361939410917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19195981146619149252547889 14396985859964361939410917)
  ·
    refine ⟨2699434848743317863639547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14396985859964361939410917 2699434848743317863639547)
    ·
      refine ⟨4049152273114976795459321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699434848743317863639547 4049152273114976795459321)
      ·
        refine ⟨3036864204836232596594491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4049152273114976795459321 3036864204836232596594491)
        ·
          refine ⟨4555296307254348894891737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036864204836232596594491 4555296307254348894891737)
          ·
            refine ⟨3416472230440761671168803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555296307254348894891737 3416472230440761671168803)
            ·
              refine ⟨5124708345661142506753205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3416472230440761671168803 5124708345661142506753205)
              ·
                refine ⟨480441407405732110008113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5124708345661142506753205 480441407405732110008113)
                ·
                  refine ⟨360331055554299082506085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480441407405732110008113 360331055554299082506085)
                  ·
                    rfl

theorem cell20_789460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_789460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789460 prefixEnd_789460 := by exact prefixLift 789460
  have htrace : WordTrace (prefixWord ++ tailWord_789460) baseStart_789460 baseEnd_789460 := by
    simpa [prefixWord, tailWord_789460, baseEnd_789460] using wordTrace_append hprefix tailTrace_789460
  have hstable : (prefixWord ++ tailWord_789460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789460).length < 2 ^ (prefixWord ++ tailWord_789460).sum := by decide
  have hdescent : baseEnd_789460 < baseStart_789460 := by decide
  rcases family_descends (prefixWord ++ tailWord_789460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789505 : List Nat := [1, 2, 4, 1, 2, 4, 2, 4]
def baseStart_789505 : Nat := 118140960795 + 789505 * 2 ^ 59
def prefixEnd_789505 : Nat := 4983230072969 + 3 ^ 40 * 789505 * 2
def baseEnd_789505 : Nat := 120117198260159642001967

theorem tailTrace_789505 : CollatzResearch.WordTrace tailWord_789505 prefixEnd_789505 120117198260159642001967 := by
  unfold tailWord_789505
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795613004765696564209969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197075336510464376139979 28795613004765696564209969)
  ·
    refine ⟨21596709753574272423157477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28795613004765696564209969 21596709753574272423157477)
    ·
      refine ⟨4049383078795176079342027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21596709753574272423157477 4049383078795176079342027)
      ·
        refine ⟨6074074618192764119013041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049383078795176079342027 6074074618192764119013041)
        ·
          refine ⟨4555555963644573089259781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074074618192764119013041 4555555963644573089259781)
          ·
            refine ⟨854166743183357454236209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4555555963644573089259781 854166743183357454236209)
            ·
              refine ⟨640625057387518090677157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854166743183357454236209 640625057387518090677157)
              ·
                refine ⟨120117198260159642001967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640625057387518090677157 120117198260159642001967)
                ·
                  rfl

theorem cell20_789505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_789505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789505 prefixEnd_789505 := by exact prefixLift 789505
  have htrace : WordTrace (prefixWord ++ tailWord_789505) baseStart_789505 baseEnd_789505 := by
    simpa [prefixWord, tailWord_789505, baseEnd_789505] using wordTrace_append hprefix tailTrace_789505
  have hstable : (prefixWord ++ tailWord_789505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789505).length < 2 ^ (prefixWord ++ tailWord_789505).sum := by decide
  have hdescent : baseEnd_789505 < baseStart_789505 := by decide
  rcases family_descends (prefixWord ++ tailWord_789505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789509 : List Nat := [1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_789509 : Nat := 118140960795 + 789509 * 2 ^ 59
def prefixEnd_789509 : Nat := 4983230072969 + 3 ^ 40 * 789509 * 2
def baseEnd_789509 : Nat := 120117806829824229957517

theorem tailTrace_789509 : CollatzResearch.WordTrace tailWord_789509 prefixEnd_789509 120117806829824229957517 := by
  unfold tailWord_789509
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795758896751205247355581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197172597834136831570387 28795758896751205247355581)
  ·
    refine ⟨10798409586281701967758343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28795758896751205247355581 10798409586281701967758343)
    ·
      refine ⟨16197614379422552951637515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10798409586281701967758343 16197614379422552951637515)
      ·
        refine ⟨24296421569133829427456273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16197614379422552951637515 24296421569133829427456273)
        ·
          refine ⟨18222316176850372070592205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24296421569133829427456273 18222316176850372070592205)
          ·
            refine ⟨6833368566318889526472077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18222316176850372070592205 6833368566318889526472077)
            ·
              refine ⟨2562513212369583572427029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6833368566318889526472077 2562513212369583572427029)
              ·
                refine ⟨120117806829824229957517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2562513212369583572427029 120117806829824229957517)
                ·
                  rfl

theorem cell20_789509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_789509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789509 prefixEnd_789509 := by exact prefixLift 789509
  have htrace : WordTrace (prefixWord ++ tailWord_789509) baseStart_789509 baseEnd_789509 := by
    simpa [prefixWord, tailWord_789509, baseEnd_789509] using wordTrace_append hprefix tailTrace_789509
  have hstable : (prefixWord ++ tailWord_789509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789509).length < 2 ^ (prefixWord ++ tailWord_789509).sum := by decide
  have hdescent : baseEnd_789509 < baseStart_789509 := by decide
  rcases family_descends (prefixWord ++ tailWord_789509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789543 : List Nat := [1, 1, 7, 1, 1, 2, 2, 5]
def baseStart_789543 : Nat := 118140960795 + 789543 * 2 ^ 59
def prefixEnd_789543 : Nat := 4983230072969 + 3 ^ 40 * 789543 * 2
def baseEnd_789543 : Nat := 120122979671973227579693

theorem tailTrace_789543 : CollatzResearch.WordTrace tailWord_789543 prefixEnd_789543 120122979671973227579693 := by
  unfold tailWord_789543
  simp only [CollatzResearch.WordTrace]
  refine ⟨28796998978628029054093283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197999319085352702728855 28796998978628029054093283)
  ·
    refine ⟨43195498467942043581139925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28796998978628029054093283 43195498467942043581139925)
    ·
      refine ⟨1012394495342391646432967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43195498467942043581139925 1012394495342391646432967)
      ·
        refine ⟨1518591743013587469649451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012394495342391646432967 1518591743013587469649451)
        ·
          refine ⟨2277887614520381204474177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518591743013587469649451 2277887614520381204474177)
          ·
            refine ⟨1708415710890285903355633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277887614520381204474177 1708415710890285903355633)
            ·
              refine ⟨1281311783167714427516725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708415710890285903355633 1281311783167714427516725)
              ·
                refine ⟨120122979671973227579693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1281311783167714427516725 120122979671973227579693)
                ·
                  rfl

theorem cell20_789543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_789543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789543 prefixEnd_789543 := by exact prefixLift 789543
  have htrace : WordTrace (prefixWord ++ tailWord_789543) baseStart_789543 baseEnd_789543 := by
    simpa [prefixWord, tailWord_789543, baseEnd_789543] using wordTrace_append hprefix tailTrace_789543
  have hstable : (prefixWord ++ tailWord_789543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789543).length < 2 ^ (prefixWord ++ tailWord_789543).sum := by decide
  have hdescent : baseEnd_789543 < baseStart_789543 := by decide
  rcases family_descends (prefixWord ++ tailWord_789543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789546 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_789546 : Nat := 118140960795 + 789546 * 2 ^ 59
def prefixEnd_789546 : Nat := 4983230072969 + 3 ^ 40 * 789546 * 2
def baseEnd_789546 : Nat := 360370308297665005639067

theorem tailTrace_789546 : CollatzResearch.WordTrace tailWord_789546 prefixEnd_789546 360370308297665005639067 := by
  unfold tailWord_789546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199277099404290141613123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19198072265078107044301661 7199277099404290141613123)
  ·
    refine ⟨10798915649106435212419685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199277099404290141613123 10798915649106435212419685)
    ·
      refine ⟨2024796684207456602328691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10798915649106435212419685 2024796684207456602328691)
      ·
        refine ⟨3037195026311184903493037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024796684207456602328691 3037195026311184903493037)
        ·
          refine ⟨1138948134866694338809889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3037195026311184903493037 1138948134866694338809889)
          ·
            refine ⟨854211101150020754107417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138948134866694338809889 854211101150020754107417)
            ·
              refine ⟨640658325862515565580563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854211101150020754107417 640658325862515565580563)
              ·
                refine ⟨960987488793773348370845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640658325862515565580563 960987488793773348370845)
                ·
                  refine ⟨360370308297665005639067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960987488793773348370845 360370308297665005639067)
                  ·
                    rfl

theorem cell20_789546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_789546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789546 prefixEnd_789546 := by exact prefixLift 789546
  have htrace : WordTrace (prefixWord ++ tailWord_789546) baseStart_789546 baseEnd_789546 := by
    simpa [prefixWord, tailWord_789546, baseEnd_789546] using wordTrace_append hprefix tailTrace_789546
  have hstable : (prefixWord ++ tailWord_789546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789546).length < 2 ^ (prefixWord ++ tailWord_789546).sum := by decide
  have hdescent : baseEnd_789546 < baseStart_789546 := by decide
  rcases family_descends (prefixWord ++ tailWord_789546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789547 : List Nat := [1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_789547 : Nat := 118140960795 + 789547 * 2 ^ 59
def prefixEnd_789547 : Nat := 4983230072969 + 3 ^ 40 * 789547 * 2
def baseEnd_789547 : Nat := 120123588241637815535243

theorem tailTrace_789547 : CollatzResearch.WordTrace tailWord_789547 prefixEnd_789547 120123588241637815535243 := by
  unfold tailWord_789547
  simp only [CollatzResearch.WordTrace]
  refine ⟨28797144870613537737238895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19198096580409025158159263 28797144870613537737238895)
  ·
    refine ⟨43195717305920306605858343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28797144870613537737238895 43195717305920306605858343)
    ·
      refine ⟨64793575958880459908787515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43195717305920306605858343 64793575958880459908787515)
      ·
        refine ⟨97190363938320689863181273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64793575958880459908787515 97190363938320689863181273)
        ·
          refine ⟨72892772953740517397385955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97190363938320689863181273 72892772953740517397385955)
          ·
            refine ⟨109339159430610776096078933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72892772953740517397385955 109339159430610776096078933)
            ·
              refine ⟨1281318274577470032375925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 109339159430610776096078933 1281318274577470032375925)
              ·
                refine ⟨120123588241637815535243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1281318274577470032375925 120123588241637815535243)
                ·
                  rfl

theorem cell20_789547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_789547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789547 prefixEnd_789547 := by exact prefixLift 789547
  have htrace : WordTrace (prefixWord ++ tailWord_789547) baseStart_789547 baseEnd_789547 := by
    simpa [prefixWord, tailWord_789547, baseEnd_789547] using wordTrace_append hprefix tailTrace_789547
  have hstable : (prefixWord ++ tailWord_789547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789547).length < 2 ^ (prefixWord ++ tailWord_789547).sum := by decide
  have hdescent : baseEnd_789547 < baseStart_789547 := by decide
  rcases family_descends (prefixWord ++ tailWord_789547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789550 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_789550 : Nat := 118140960795 + 789550 * 2 ^ 59
def prefixEnd_789550 : Nat := 4983230072969 + 3 ^ 40 * 789550 * 2
def baseEnd_789550 : Nat := 360372134006658769505717

theorem tailTrace_789550 : CollatzResearch.WordTrace tailWord_789550 prefixEnd_789550 360372134006658769505717 := by
  unfold tailWord_789550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599656786200333656199763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19198169526401779499732069 3599656786200333656199763)
  ·
    refine ⟨5399485179300500484299645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599656786200333656199763 5399485179300500484299645)
    ·
      refine ⟨2024806942237687681612367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5399485179300500484299645 2024806942237687681612367)
      ·
        refine ⟨3037210413356531522418551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024806942237687681612367 3037210413356531522418551)
        ·
          refine ⟨4555815620034797283627827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037210413356531522418551 4555815620034797283627827)
          ·
            refine ⟨6833723430052195925441741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555815620034797283627827 6833723430052195925441741)
            ·
              refine ⟨2562646286269573472040653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6833723430052195925441741 2562646286269573472040653)
              ·
                refine ⟨960992357351090052015245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562646286269573472040653 960992357351090052015245)
                ·
                  refine ⟨360372134006658769505717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960992357351090052015245 360372134006658769505717)
                  ·
                    rfl

theorem cell20_789550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_789550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789550 prefixEnd_789550 := by exact prefixLift 789550
  have htrace : WordTrace (prefixWord ++ tailWord_789550) baseStart_789550 baseEnd_789550 := by
    simpa [prefixWord, tailWord_789550, baseEnd_789550] using wordTrace_append hprefix tailTrace_789550
  have hstable : (prefixWord ++ tailWord_789550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789550).length < 2 ^ (prefixWord ++ tailWord_789550).sum := by decide
  have hdescent : baseEnd_789550 < baseStart_789550 := by decide
  rcases family_descends (prefixWord ++ tailWord_789550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789598 : List Nat := [4, 4, 1, 1, 1, 1, 3, 5]
def baseStart_789598 : Nat := 118140960795 + 789598 * 2 ^ 59
def prefixEnd_789598 : Nat := 4983230072969 + 3 ^ 40 * 789598 * 2
def baseEnd_789598 : Nat := 120131347504861311968507

theorem tailTrace_789598 : CollatzResearch.WordTrace tailWord_789598 prefixEnd_789598 120131347504861311968507 := by
  unfold tailWord_789598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599875624178596680918181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19199336662285848964896965 3599875624178596680918181)
  ·
    refine ⟨674976679533486877672159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3599875624178596680918181 674976679533486877672159)
    ·
      refine ⟨1012465019300230316508239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674976679533486877672159 1012465019300230316508239)
      ·
        refine ⟨1518697528950345474762359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012465019300230316508239 1518697528950345474762359)
        ·
          refine ⟨2278046293425518212143539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518697528950345474762359 2278046293425518212143539)
          ·
            refine ⟨3417069440138277318215309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278046293425518212143539 3417069440138277318215309)
            ·
              refine ⟨1281401040051853994330741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3417069440138277318215309 1281401040051853994330741)
              ·
                refine ⟨120131347504861311968507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1281401040051853994330741 120131347504861311968507)
                ·
                  rfl

theorem cell20_789598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_789598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789598 prefixEnd_789598 := by exact prefixLift 789598
  have htrace : WordTrace (prefixWord ++ tailWord_789598) baseStart_789598 baseEnd_789598 := by
    simpa [prefixWord, tailWord_789598, baseEnd_789598] using wordTrace_append hprefix tailTrace_789598
  have hstable : (prefixWord ++ tailWord_789598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789598).length < 2 ^ (prefixWord ++ tailWord_789598).sum := by decide
  have hdescent : baseEnd_789598 < baseStart_789598 := by decide
  rcases family_descends (prefixWord ++ tailWord_789598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789609 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_789609 : Nat := 118140960795 + 789609 * 2 ^ 59
def prefixEnd_789609 : Nat := 4983230072969 + 3 ^ 40 * 789609 * 2
def baseEnd_789609 : Nat := 360399063214316786538809

theorem tailTrace_789609 : CollatzResearch.WordTrace tailWord_789609 prefixEnd_789609 360399063214316786538809 := by
  unfold tailWord_789609
  simp only [CollatzResearch.WordTrace]
  refine ⟨28799406196388922325995881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19199604130925948217330587 28799406196388922325995881)
  ·
    refine ⟨21599554647291691744496911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28799406196388922325995881 21599554647291691744496911)
    ·
      refine ⟨32399331970937537616745367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21599554647291691744496911 32399331970937537616745367)
      ·
        refine ⟨48598997956406306425118051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32399331970937537616745367 48598997956406306425118051)
        ·
          refine ⟨72898496934609459637677077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48598997956406306425118051 72898496934609459637677077)
          ·
            refine ⟨3417117043809818420516113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72898496934609459637677077 3417117043809818420516113)
            ·
              refine ⟨2562837782857363815387085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417117043809818420516113 2562837782857363815387085)
              ·
                refine ⟨961064168571511430770157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562837782857363815387085 961064168571511430770157)
                ·
                  refine ⟨360399063214316786538809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961064168571511430770157 360399063214316786538809)
                  ·
                    rfl

theorem cell20_789609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_789609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789609 prefixEnd_789609 := by exact prefixLift 789609
  have htrace : WordTrace (prefixWord ++ tailWord_789609) baseStart_789609 baseEnd_789609 := by
    simpa [prefixWord, tailWord_789609, baseEnd_789609] using wordTrace_append hprefix tailTrace_789609
  have hstable : (prefixWord ++ tailWord_789609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789609).length < 2 ^ (prefixWord ++ tailWord_789609).sum := by decide
  have hdescent : baseEnd_789609 < baseStart_789609 := by decide
  rcases family_descends (prefixWord ++ tailWord_789609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789616 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_789616 : Nat := 118140960795 + 789616 * 2 ^ 59
def prefixEnd_789616 : Nat := 4983230072969 + 3 ^ 40 * 789616 * 2
def baseEnd_789616 : Nat := 360402258205055873305447

theorem tailTrace_789616 : CollatzResearch.WordTrace tailWord_789616 prefixEnd_789616 360402258205055873305447 := by
  unfold tailWord_789616
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399830753681781260750351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19199774338242375014333801 14399830753681781260750351)
  ·
    refine ⟨21599746130522671891125527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14399830753681781260750351 21599746130522671891125527)
    ·
      refine ⟨32399619195784007836688291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21599746130522671891125527 32399619195784007836688291)
      ·
        refine ⟨48599428793676011755032437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32399619195784007836688291 48599428793676011755032437)
        ·
          refine ⟨4556196449407126102034291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48599428793676011755032437 4556196449407126102034291)
          ·
            refine ⟨6834294674110689153051437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556196449407126102034291 6834294674110689153051437)
            ·
              refine ⟨2562860502791508432394289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6834294674110689153051437 2562860502791508432394289)
              ·
                refine ⟨1922145377093631324295717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562860502791508432394289 1922145377093631324295717)
                ·
                  refine ⟨360402258205055873305447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1922145377093631324295717 360402258205055873305447)
                  ·
                    rfl

theorem cell20_789616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_789616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789616 prefixEnd_789616 := by exact prefixLift 789616
  have htrace : WordTrace (prefixWord ++ tailWord_789616) baseStart_789616 baseEnd_789616 := by
    simpa [prefixWord, tailWord_789616, baseEnd_789616] using wordTrace_append hprefix tailTrace_789616
  have hstable : (prefixWord ++ tailWord_789616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789616).length < 2 ^ (prefixWord ++ tailWord_789616).sum := by decide
  have hdescent : baseEnd_789616 < baseStart_789616 := by decide
  rcases family_descends (prefixWord ++ tailWord_789616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789640 : List Nat := [2, 1, 3, 4, 2, 1, 7]
def baseStart_789640 : Nat := 118140960795 + 789640 * 2 ^ 59
def prefixEnd_789640 : Nat := 4983230072969 + 3 ^ 40 * 789640 * 2
def baseEnd_789640 : Nat := 40045912495446495167261

theorem tailTrace_789640 : CollatzResearch.WordTrace tailWord_789640 prefixEnd_789640 40045912495446495167261 := by
  unfold tailWord_789640
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400268429638307310187187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19200357906184409746916249 14400268429638307310187187)
  ·
    refine ⟨21600402644457460965280781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14400268429638307310187187 21600402644457460965280781)
    ·
      refine ⟨8100150991671547861980293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21600402644457460965280781 8100150991671547861980293)
      ·
        refine ⟨1518778310938415224121305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8100150991671547861980293 1518778310938415224121305)
        ·
          refine ⟨1139083733203811418090979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518778310938415224121305 1139083733203811418090979)
          ·
            refine ⟨1708625599805717127136469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139083733203811418090979 1708625599805717127136469)
            ·
              refine ⟨40045912495446495167261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1708625599805717127136469 40045912495446495167261)
              ·
                rfl

theorem cell20_789640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 7].length) (baseStart_789640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789640 prefixEnd_789640 := by exact prefixLift 789640
  have htrace : WordTrace (prefixWord ++ tailWord_789640) baseStart_789640 baseEnd_789640 := by
    simpa [prefixWord, tailWord_789640, baseEnd_789640] using wordTrace_append hprefix tailTrace_789640
  have hstable : (prefixWord ++ tailWord_789640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789640).length < 2 ^ (prefixWord ++ tailWord_789640).sum := by decide
  have hdescent : baseEnd_789640 < baseStart_789640 := by decide
  rcases family_descends (prefixWord ++ tailWord_789640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789650 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_789650 : Nat := 118140960795 + 789650 * 2 ^ 59
def prefixEnd_789650 : Nat := 4983230072969 + 3 ^ 40 * 789650 * 2
def baseEnd_789650 : Nat := 360417776731502866171975

theorem tailTrace_789650 : CollatzResearch.WordTrace tailWord_789650 prefixEnd_789650 360417776731502866171975 := by
  unfold tailWord_789650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200225397310096582059601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19200601059493590885492269 7200225397310096582059601)
  ·
    refine ⟨5400169047982572436544701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7200225397310096582059601 5400169047982572436544701)
    ·
      refine ⟨2025063392993464663704263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5400169047982572436544701 2025063392993464663704263)
      ·
        refine ⟨3037595089490196995556395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025063392993464663704263 3037595089490196995556395)
        ·
          refine ⟨4556392634235295493334593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037595089490196995556395 4556392634235295493334593)
          ·
            refine ⟨3417294475676471620000945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4556392634235295493334593 3417294475676471620000945)
            ·
              refine ⟨2562970856757353715000709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417294475676471620000945 2562970856757353715000709)
              ·
                refine ⟨480557035642003821562633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2562970856757353715000709 480557035642003821562633)
                ·
                  refine ⟨360417776731502866171975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480557035642003821562633 360417776731502866171975)
                  ·
                    rfl

theorem cell20_789650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_789650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789650 prefixEnd_789650 := by exact prefixLift 789650
  have htrace : WordTrace (prefixWord ++ tailWord_789650) baseStart_789650 baseEnd_789650 := by
    simpa [prefixWord, tailWord_789650, baseEnd_789650] using wordTrace_append hprefix tailTrace_789650
  have hstable : (prefixWord ++ tailWord_789650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789650).length < 2 ^ (prefixWord ++ tailWord_789650).sum := by decide
  have hdescent : baseEnd_789650 < baseStart_789650 := by decide
  rcases family_descends (prefixWord ++ tailWord_789650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789661 : List Nat := [1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_789661 : Nat := 118140960795 + 789661 * 2 ^ 59
def prefixEnd_789661 : Nat := 4983230072969 + 3 ^ 40 * 789661 * 2
def baseEnd_789661 : Nat := 120140932477078572268421

theorem tailTrace_789661 : CollatzResearch.WordTrace tailWord_789661 prefixEnd_789661 120140932477078572268421 := by
  unfold tailWord_789661
  simp only [CollatzResearch.WordTrace]
  refine ⟨28801302792200535206888837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19200868528133690137925891 28801302792200535206888837)
  ·
    refine ⟨5400244273537600351291657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28801302792200535206888837 5400244273537600351291657)
    ·
      refine ⟨4050183205153200263468743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5400244273537600351291657 4050183205153200263468743)
      ·
        refine ⟨6075274807729800395203115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050183205153200263468743 6075274807729800395203115)
        ·
          refine ⟨9112912211594700592804673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075274807729800395203115 9112912211594700592804673)
          ·
            refine ⟨6834684158696025444603505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9112912211594700592804673 6834684158696025444603505)
            ·
              refine ⟨5126013119022019083452629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834684158696025444603505 5126013119022019083452629)
              ·
                refine ⟨120140932477078572268421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5126013119022019083452629 120140932477078572268421)
                ·
                  rfl

theorem cell20_789661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_789661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789661 prefixEnd_789661 := by exact prefixLift 789661
  have htrace : WordTrace (prefixWord ++ tailWord_789661) baseStart_789661 baseEnd_789661 := by
    simpa [prefixWord, tailWord_789661, baseEnd_789661] using wordTrace_append hprefix tailTrace_789661
  have hstable : (prefixWord ++ tailWord_789661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789661).length < 2 ^ (prefixWord ++ tailWord_789661).sum := by decide
  have hdescent : baseEnd_789661 < baseStart_789661 := by decide
  rcases family_descends (prefixWord ++ tailWord_789661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789664 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_789664 : Nat := 118140960795 + 789664 * 2 ^ 59
def prefixEnd_789664 : Nat := 4983230072969 + 3 ^ 40 * 789664 * 2
def baseEnd_789664 : Nat := 360424166712981039705251

theorem tailTrace_789664 : CollatzResearch.WordTrace tailWord_789664 prefixEnd_789664 360424166712981039705251 := by
  unfold tailWord_789664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400706105594833359624023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19200941474126444479498697 14400706105594833359624023)
  ·
    refine ⟨21601059158392250039436035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14400706105594833359624023 21601059158392250039436035)
    ·
      refine ⟨32401588737588375059154053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21601059158392250039436035 32401588737588375059154053)
      ·
        refine ⟨6075297888297820323591385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32401588737588375059154053 6075297888297820323591385)
        ·
          refine ⟨4556473416223365242693539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6075297888297820323591385 4556473416223365242693539)
          ·
            refine ⟨6834710124335047864040309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556473416223365242693539 6834710124335047864040309)
            ·
              refine ⟨640754074156410737253779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6834710124335047864040309 640754074156410737253779)
              ·
                refine ⟨961131111234616105880669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640754074156410737253779 961131111234616105880669)
                ·
                  refine ⟨360424166712981039705251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961131111234616105880669 360424166712981039705251)
                  ·
                    rfl

theorem cell20_789664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_789664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789664 prefixEnd_789664 := by exact prefixLift 789664
  have htrace : WordTrace (prefixWord ++ tailWord_789664) baseStart_789664 baseEnd_789664 := by
    simpa [prefixWord, tailWord_789664, baseEnd_789664] using wordTrace_append hprefix tailTrace_789664
  have hstable : (prefixWord ++ tailWord_789664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789664).length < 2 ^ (prefixWord ++ tailWord_789664).sum := by decide
  have hdescent : baseEnd_789664 < baseStart_789664 := by decide
  rcases family_descends (prefixWord ++ tailWord_789664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789671 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_789671 : Nat := 118140960795 + 789671 * 2 ^ 59
def prefixEnd_789671 : Nat := 4983230072969 + 3 ^ 40 * 789671 * 2
def baseEnd_789671 : Nat := 360427361703720126471889

theorem tailTrace_789671 : CollatzResearch.WordTrace tailWord_789671 prefixEnd_789671 360427361703720126471889 := by
  unfold tailWord_789671
  simp only [CollatzResearch.WordTrace]
  refine ⟨28801667522164306914752867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19201111681442871276501911 28801667522164306914752867)
  ·
    refine ⟨43202501283246460372129301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28801667522164306914752867 43202501283246460372129301)
    ·
      refine ⟨2025117247652177829943561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43202501283246460372129301 2025117247652177829943561)
      ·
        refine ⟨1518837935739133372457671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025117247652177829943561 1518837935739133372457671)
        ·
          refine ⟨2278256903608700058686507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518837935739133372457671 2278256903608700058686507)
          ·
            refine ⟨3417385355413050088029761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278256903608700058686507 3417385355413050088029761)
            ·
              refine ⟨2563039016559787566022321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417385355413050088029761 2563039016559787566022321)
              ·
                refine ⟨1922279262419840674516741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563039016559787566022321 1922279262419840674516741)
                ·
                  refine ⟨360427361703720126471889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1922279262419840674516741 360427361703720126471889)
                  ·
                    rfl

theorem cell20_789671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_789671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789671 prefixEnd_789671 := by exact prefixLift 789671
  have htrace : WordTrace (prefixWord ++ tailWord_789671) baseStart_789671 baseEnd_789671 := by
    simpa [prefixWord, tailWord_789671, baseEnd_789671] using wordTrace_append hprefix tailTrace_789671
  have hstable : (prefixWord ++ tailWord_789671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789671).length < 2 ^ (prefixWord ++ tailWord_789671).sum := by decide
  have hdescent : baseEnd_789671 < baseStart_789671 := by decide
  rcases family_descends (prefixWord ++ tailWord_789671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789674 : List Nat := [3, 1, 5, 1, 1, 3, 2, 4]
def baseStart_789674 : Nat := 118140960795 + 789674 * 2 ^ 59
def prefixEnd_789674 : Nat := 4983230072969 + 3 ^ 40 * 789674 * 2
def baseEnd_789674 : Nat := 120142910328488483123959

theorem tailTrace_789674 : CollatzResearch.WordTrace tailWord_789674 prefixEnd_789674 120142910328488483123959 := by
  unfold tailWord_789674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200444235288359606778019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19201184627435625618074717 7200444235288359606778019)
  ·
    refine ⟨10800666352932539410167029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7200444235288359606778019 10800666352932539410167029)
    ·
      refine ⟨1012562470587425569703159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10800666352932539410167029 1012562470587425569703159)
      ·
        refine ⟨1518843705881138354554739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012562470587425569703159 1518843705881138354554739)
        ·
          refine ⟨2278265558821707531832109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518843705881138354554739 2278265558821707531832109)
          ·
            refine ⟨854349584558140324437041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2278265558821707531832109 854349584558140324437041)
            ·
              refine ⟨640762188418605243327781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854349584558140324437041 640762188418605243327781)
              ·
                refine ⟨120142910328488483123959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640762188418605243327781 120142910328488483123959)
                ·
                  rfl

theorem cell20_789674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_789674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789674 prefixEnd_789674 := by exact prefixLift 789674
  have htrace : WordTrace (prefixWord ++ tailWord_789674) baseStart_789674 baseEnd_789674 := by
    simpa [prefixWord, tailWord_789674, baseEnd_789674] using wordTrace_append hprefix tailTrace_789674
  have hstable : (prefixWord ++ tailWord_789674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789674).length < 2 ^ (prefixWord ++ tailWord_789674).sum := by decide
  have hdescent : baseEnd_789674 < baseStart_789674 := by decide
  rcases family_descends (prefixWord ++ tailWord_789674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789751 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_789751 : Nat := 118140960795 + 789751 * 2 ^ 59
def prefixEnd_789751 : Nat := 4983230072969 + 3 ^ 40 * 789751 * 2
def baseEnd_789751 : Nat := 360463875883595403804895

theorem tailTrace_789751 : CollatzResearch.WordTrace tailWord_789751 prefixEnd_789751 360463875883595403804895 := by
  unfold tailWord_789751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28804585361874480577665107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19203056907916320385110071 28804585361874480577665107)
  ·
    refine ⟨43206878042811720866497661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28804585361874480577665107 43206878042811720866497661)
    ·
      refine ⟨16202579266054395324936623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43206878042811720866497661 16202579266054395324936623)
      ·
        refine ⟨24303868899081592987404935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16202579266054395324936623 24303868899081592987404935)
        ·
          refine ⟨36455803348622389481107403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24303868899081592987404935 36455803348622389481107403)
          ·
            refine ⟨54683705022933584221661105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36455803348622389481107403 54683705022933584221661105)
            ·
              refine ⟨41012778767200188166245829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54683705022933584221661105 41012778767200188166245829)
              ·
                refine ⟨7689896018850035281171093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41012778767200188166245829 7689896018850035281171093)
                ·
                  refine ⟨360463875883595403804895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7689896018850035281171093 360463875883595403804895)
                  ·
                    rfl

theorem cell20_789751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_789751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789751 prefixEnd_789751 := by exact prefixLift 789751
  have htrace : WordTrace (prefixWord ++ tailWord_789751) baseStart_789751 baseEnd_789751 := by
    simpa [prefixWord, tailWord_789751, baseEnd_789751] using wordTrace_append hprefix tailTrace_789751
  have hstable : (prefixWord ++ tailWord_789751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789751).length < 2 ^ (prefixWord ++ tailWord_789751).sum := by decide
  have hdescent : baseEnd_789751 < baseStart_789751 := by decide
  rcases family_descends (prefixWord ++ tailWord_789751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789761 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_789761 : Nat := 118140960795 + 789761 * 2 ^ 59
def prefixEnd_789761 : Nat := 4983230072969 + 3 ^ 40 * 789761 * 2
def baseEnd_789761 : Nat := 360468440156079813471521

theorem tailTrace_789761 : CollatzResearch.WordTrace tailWord_789761 prefixEnd_789761 360468440156079813471521 := by
  unfold tailWord_789761
  simp only [CollatzResearch.WordTrace]
  refine ⟨28804950091838252285529137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19203300061225501523686091 28804950091838252285529137)
  ·
    refine ⟨21603712568878689214146853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28804950091838252285529137 21603712568878689214146853)
    ·
      refine ⟨4050696106664754227652535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21603712568878689214146853 4050696106664754227652535)
      ·
        refine ⟨6076044159997131341478803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050696106664754227652535 6076044159997131341478803)
        ·
          refine ⟨9114066239995697012218205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076044159997131341478803 9114066239995697012218205)
          ·
            refine ⟨3417774839998386379581827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9114066239995697012218205 3417774839998386379581827)
            ·
              refine ⟨5126662259997579569372741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417774839998386379581827 5126662259997579569372741)
              ·
                refine ⟨961249173749546169257389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5126662259997579569372741 961249173749546169257389)
                ·
                  refine ⟨360468440156079813471521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961249173749546169257389 360468440156079813471521)
                  ·
                    rfl

theorem cell20_789761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_789761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789761 prefixEnd_789761 := by exact prefixLift 789761
  have htrace : WordTrace (prefixWord ++ tailWord_789761) baseStart_789761 baseEnd_789761 := by
    simpa [prefixWord, tailWord_789761, baseEnd_789761] using wordTrace_append hprefix tailTrace_789761
  have hstable : (prefixWord ++ tailWord_789761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789761).length < 2 ^ (prefixWord ++ tailWord_789761).sum := by decide
  have hdescent : baseEnd_789761 < baseStart_789761 := by decide
  rcases family_descends (prefixWord ++ tailWord_789761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789764 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 2]
def baseStart_789764 : Nat := 118140960795 + 789764 * 2 ^ 59
def prefixEnd_789764 : Nat := 4983230072969 + 3 ^ 40 * 789764 * 2
def baseEnd_789764 : Nat := 360469809437825136371509

theorem tailTrace_789764 : CollatzResearch.WordTrace tailWord_789764 prefixEnd_789764 360469809437825136371509 := by
  unfold tailWord_789764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402529755413691898944173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19203373007218255865258897 14402529755413691898944173)
  ·
    refine ⟨5400948658280134462104065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14402529755413691898944173 5400948658280134462104065)
    ·
      refine ⟨4050711493710100846578049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5400948658280134462104065 4050711493710100846578049)
      ·
        refine ⟨3038033620282575634933537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4050711493710100846578049 3038033620282575634933537)
        ·
          refine ⟨2278525215211931726200153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3038033620282575634933537 2278525215211931726200153)
          ·
            refine ⟨1708893911408948794650115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278525215211931726200153 1708893911408948794650115)
            ·
              refine ⟨2563340867113423191975173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708893911408948794650115 2563340867113423191975173)
              ·
                refine ⟨480626412583766848495345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2563340867113423191975173 480626412583766848495345)
                ·
                  refine ⟨360469809437825136371509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480626412583766848495345 360469809437825136371509)
                  ·
                    rfl

theorem cell20_789764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_789764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789764 prefixEnd_789764 := by exact prefixLift 789764
  have htrace : WordTrace (prefixWord ++ tailWord_789764) baseStart_789764 baseEnd_789764 := by
    simpa [prefixWord, tailWord_789764, baseEnd_789764] using wordTrace_append hprefix tailTrace_789764
  have hstable : (prefixWord ++ tailWord_789764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789764).length < 2 ^ (prefixWord ++ tailWord_789764).sum := by decide
  have hdescent : baseEnd_789764 < baseStart_789764 := by decide
  rcases family_descends (prefixWord ++ tailWord_789764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789802 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_789802 : Nat := 118140960795 + 789802 * 2 ^ 59
def prefixEnd_789802 : Nat := 4983230072969 + 3 ^ 40 * 789802 * 2
def baseEnd_789802 : Nat := 360487153673265893104687

theorem tailTrace_789802 : CollatzResearch.WordTrace tailWord_789802 prefixEnd_789802 360487153673265893104687 := by
  unfold tailWord_789802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201611371172429071942915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19204296989793144191847773 7201611371172429071942915)
  ·
    refine ⟨10802417056758643607914373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7201611371172429071942915 10802417056758643607914373)
    ·
      refine ⟨2025453198142245676483945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10802417056758643607914373 2025453198142245676483945)
      ·
        refine ⟨1519089898606684257362959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025453198142245676483945 1519089898606684257362959)
        ·
          refine ⟨2278634847910026386044439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519089898606684257362959 2278634847910026386044439)
          ·
            refine ⟨3417952271865039579066659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278634847910026386044439 3417952271865039579066659)
            ·
              refine ⟨5126928407797559368599989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417952271865039579066659 5126928407797559368599989)
              ·
                refine ⟨480649538231021190806249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5126928407797559368599989 480649538231021190806249)
                ·
                  refine ⟨360487153673265893104687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480649538231021190806249 360487153673265893104687)
                  ·
                    rfl

theorem cell20_789802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_789802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789802 prefixEnd_789802 := by exact prefixLift 789802
  have htrace : WordTrace (prefixWord ++ tailWord_789802) baseStart_789802 baseEnd_789802 := by
    simpa [prefixWord, tailWord_789802, baseEnd_789802] using wordTrace_append hprefix tailTrace_789802
  have hstable : (prefixWord ++ tailWord_789802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789802).length < 2 ^ (prefixWord ++ tailWord_789802).sum := by decide
  have hdescent : baseEnd_789802 < baseStart_789802 := by decide
  rcases family_descends (prefixWord ++ tailWord_789802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789813 : List Nat := [1, 3, 3, 1, 2, 3, 7]
def baseStart_789813 : Nat := 118140960795 + 789813 * 2 ^ 59
def prefixEnd_789813 : Nat := 4983230072969 + 3 ^ 40 * 789813 * 2
def baseEnd_789813 : Nat := 40054686041444304859775

theorem tailTrace_789813 : CollatzResearch.WordTrace tailWord_789813 prefixEnd_789813 40054686041444304859775 := by
  unfold tailWord_789813
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806846687649865166422093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19204564458433243444281395 28806846687649865166422093)
  ·
    refine ⟨10802567507868699437408285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28806846687649865166422093 10802567507868699437408285)
    ·
      refine ⟨4050962815450762289028107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10802567507868699437408285 4050962815450762289028107)
      ·
        refine ⟨6076444223176143433542161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050962815450762289028107 6076444223176143433542161)
        ·
          refine ⟨4557333167382107575156621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6076444223176143433542161 4557333167382107575156621)
          ·
            refine ⟨1708999937768290340683733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4557333167382107575156621 1708999937768290340683733)
            ·
              refine ⟨40054686041444304859775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1708999937768290340683733 40054686041444304859775)
              ·
                rfl

theorem cell20_789813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_789813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789813 prefixEnd_789813 := by exact prefixLift 789813
  have htrace : WordTrace (prefixWord ++ tailWord_789813) baseStart_789813 baseEnd_789813 := by
    simpa [prefixWord, tailWord_789813, baseEnd_789813] using wordTrace_append hprefix tailTrace_789813
  have hstable : (prefixWord ++ tailWord_789813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789813).length < 2 ^ (prefixWord ++ tailWord_789813).sum := by decide
  have hdescent : baseEnd_789813 < baseStart_789813 := by decide
  rcases family_descends (prefixWord ++ tailWord_789813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789823 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 2]
def baseStart_789823 : Nat := 118140960795 + 789823 * 2 ^ 59
def prefixEnd_789823 : Nat := 4983230072969 + 3 ^ 40 * 789823 * 2
def baseEnd_789823 : Nat := 360496738645483153404601

theorem tailTrace_789823 : CollatzResearch.WordTrace tailWord_789823 prefixEnd_789823 360496738645483153404601 := by
  unfold tailWord_789823
  simp only [CollatzResearch.WordTrace]
  refine ⟨28807211417613636874286123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19204807611742424582857415 28807211417613636874286123)
  ·
    refine ⟨43210817126420455311429185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28807211417613636874286123 43210817126420455311429185)
    ·
      refine ⟨32408112844815341483571889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43210817126420455311429185 32408112844815341483571889)
      ·
        refine ⟨24306084633611506112678917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32408112844815341483571889 24306084633611506112678917)
        ·
          refine ⟨4557390868802157396127297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24306084633611506112678917 4557390868802157396127297)
          ·
            refine ⟨3418043151601618047095473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4557390868802157396127297 3418043151601618047095473)
            ·
              refine ⟨2563532363701213535321605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418043151601618047095473 2563532363701213535321605)
              ·
                refine ⟨480662318193977537872801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2563532363701213535321605 480662318193977537872801)
                ·
                  refine ⟨360496738645483153404601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480662318193977537872801 360496738645483153404601)
                  ·
                    rfl

theorem cell20_789823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 2].length) (baseStart_789823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789823 prefixEnd_789823 := by exact prefixLift 789823
  have htrace : WordTrace (prefixWord ++ tailWord_789823) baseStart_789823 baseEnd_789823 := by
    simpa [prefixWord, tailWord_789823, baseEnd_789823] using wordTrace_append hprefix tailTrace_789823
  have hstable : (prefixWord ++ tailWord_789823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789823).length < 2 ^ (prefixWord ++ tailWord_789823).sum := by decide
  have hdescent : baseEnd_789823 < baseStart_789823 := by decide
  rcases family_descends (prefixWord ++ tailWord_789823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789844 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_789844 : Nat := 118140960795 + 789844 * 2 ^ 59
def prefixEnd_789844 : Nat := 4983230072969 + 3 ^ 40 * 789844 * 2
def baseEnd_789844 : Nat := 360506323617700413704515

theorem tailTrace_789844 : CollatzResearch.WordTrace tailWord_789844 prefixEnd_789844 360506323617700413704515 := by
  unfold tailWord_789844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403988675268778730400293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19205318233691704973867057 14403988675268778730400293)
  ·
    refine ⟨2700747876612896011950055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14403988675268778730400293 2700747876612896011950055)
    ·
      refine ⟨4051121814919344017925083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700747876612896011950055 4051121814919344017925083)
      ·
        refine ⟨6076682722379016026887625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051121814919344017925083 6076682722379016026887625)
        ·
          refine ⟨4557512041784262020165719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6076682722379016026887625 4557512041784262020165719)
          ·
            refine ⟨6836268062676393030248579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4557512041784262020165719 6836268062676393030248579)
            ·
              refine ⟨10254402094014589545372869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836268062676393030248579 10254402094014589545372869)
              ·
                refine ⟨1922700392627735539757413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10254402094014589545372869 1922700392627735539757413)
                ·
                  refine ⟨360506323617700413704515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1922700392627735539757413 360506323617700413704515)
                  ·
                    rfl

theorem cell20_789844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_789844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789844 prefixEnd_789844 := by exact prefixLift 789844
  have htrace : WordTrace (prefixWord ++ tailWord_789844) baseStart_789844 baseEnd_789844 := by
    simpa [prefixWord, tailWord_789844, baseEnd_789844] using wordTrace_append hprefix tailTrace_789844
  have hstable : (prefixWord ++ tailWord_789844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789844).length < 2 ^ (prefixWord ++ tailWord_789844).sum := by decide
  have hdescent : baseEnd_789844 < baseStart_789844 := by decide
  rcases family_descends (prefixWord ++ tailWord_789844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789853 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 2]
def baseStart_789853 : Nat := 118140960795 + 789853 * 2 ^ 59
def prefixEnd_789853 : Nat := 4983230072969 + 3 ^ 40 * 789853 * 2
def baseEnd_789853 : Nat := 360510431462936382404479

theorem tailTrace_789853 : CollatzResearch.WordTrace tailWord_789853 prefixEnd_789853 360510431462936382404479 := by
  unfold tailWord_789853
  simp only [CollatzResearch.WordTrace]
  refine ⟨28808305607504951997878213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19205537071669967998585475 28808305607504951997878213)
  ·
    refine ⟨5401557301407178499602165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28808305607504951997878213 5401557301407178499602165)
    ·
      refine ⟨506395997006922984337703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5401557301407178499602165 506395997006922984337703)
      ·
        refine ⟨759593995510384476506555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506395997006922984337703 759593995510384476506555)
        ·
          refine ⟨1139390993265576714759833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759593995510384476506555 1139390993265576714759833)
          ·
            refine ⟨854543244949182536069875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139390993265576714759833 854543244949182536069875)
            ·
              refine ⟨1281814867423773804104813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854543244949182536069875 1281814867423773804104813)
              ·
                refine ⟨480680575283915176539305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1281814867423773804104813 480680575283915176539305)
                ·
                  refine ⟨360510431462936382404479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480680575283915176539305 360510431462936382404479)
                  ·
                    rfl

theorem cell20_789853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_789853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789853 prefixEnd_789853 := by exact prefixLift 789853
  have htrace : WordTrace (prefixWord ++ tailWord_789853) baseStart_789853 baseEnd_789853 := by
    simpa [prefixWord, tailWord_789853, baseEnd_789853] using wordTrace_append hprefix tailTrace_789853
  have hstable : (prefixWord ++ tailWord_789853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789853).length < 2 ^ (prefixWord ++ tailWord_789853).sum := by decide
  have hdescent : baseEnd_789853 < baseStart_789853 := by decide
  rcases family_descends (prefixWord ++ tailWord_789853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789892 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_789892 : Nat := 118140960795 + 789892 * 2 ^ 59
def prefixEnd_789892 : Nat := 4983230072969 + 3 ^ 40 * 789892 * 2
def baseEnd_789892 : Nat := 360528232125625580104319

theorem tailTrace_789892 : CollatzResearch.WordTrace tailWord_789892 prefixEnd_789892 360528232125625580104319 := by
  unfold tailWord_789892
  simp only [CollatzResearch.WordTrace]
  refine ⟨14404864027181830829273965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19206485369575774439031953 14404864027181830829273965)
  ·
    refine ⟨5401824010193186560977737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14404864027181830829273965 5401824010193186560977737)
    ·
      refine ⟨4051368007644889920733303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5401824010193186560977737 4051368007644889920733303)
      ·
        refine ⟨6077052011467334881099955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051368007644889920733303 6077052011467334881099955)
        ·
          refine ⟨9115578017201002321649933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6077052011467334881099955 9115578017201002321649933)
          ·
            refine ⟨3418341756450375870618725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9115578017201002321649933 3418341756450375870618725)
            ·
              refine ⟨640939079334445475741011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3418341756450375870618725 640939079334445475741011)
              ·
                refine ⟨961408619001668213611517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640939079334445475741011 961408619001668213611517)
                ·
                  refine ⟨360528232125625580104319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961408619001668213611517 360528232125625580104319)
                  ·
                    rfl

theorem cell20_789892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_789892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789892 prefixEnd_789892 := by exact prefixLift 789892
  have htrace : WordTrace (prefixWord ++ tailWord_789892) baseStart_789892 baseEnd_789892 := by
    simpa [prefixWord, tailWord_789892, baseEnd_789892] using wordTrace_append hprefix tailTrace_789892
  have hstable : (prefixWord ++ tailWord_789892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789892).length < 2 ^ (prefixWord ++ tailWord_789892).sum := by decide
  have hdescent : baseEnd_789892 < baseStart_789892 := by decide
  rcases family_descends (prefixWord ++ tailWord_789892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789933 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 2]
def baseStart_789933 : Nat := 118140960795 + 789933 * 2 ^ 59
def prefixEnd_789933 : Nat := 4983230072969 + 3 ^ 40 * 789933 * 2
def baseEnd_789933 : Nat := 360546945642811659737485

theorem tailTrace_789933 : CollatzResearch.WordTrace tailWord_789933 prefixEnd_789933 360546945642811659737485 := by
  unfold tailWord_789933
  simp only [CollatzResearch.WordTrace]
  refine ⟨28811223447215125660790453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19207482298143417107193635 28811223447215125660790453)
  ·
    refine ⟨2701052198176418030699105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28811223447215125660790453 2701052198176418030699105)
    ·
      refine ⟨2025789148632313523024329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701052198176418030699105 2025789148632313523024329)
      ·
        refine ⟨1519341861474235142268247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025789148632313523024329 1519341861474235142268247)
        ·
          refine ⟨2279012792211352713402371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519341861474235142268247 2279012792211352713402371)
          ·
            refine ⟨3418519188317029070103557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279012792211352713402371 3418519188317029070103557)
            ·
              refine ⟨640972347809442950644417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3418519188317029070103557 640972347809442950644417)
              ·
                refine ⟨480729260857082212983313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640972347809442950644417 480729260857082212983313)
                ·
                  refine ⟨360546945642811659737485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480729260857082212983313 360546945642811659737485)
                  ·
                    rfl

theorem cell20_789933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_789933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789933 prefixEnd_789933 := by exact prefixLift 789933
  have htrace : WordTrace (prefixWord ++ tailWord_789933) baseStart_789933 baseEnd_789933 := by
    simpa [prefixWord, tailWord_789933, baseEnd_789933] using wordTrace_append hprefix tailTrace_789933
  have hstable : (prefixWord ++ tailWord_789933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789933).length < 2 ^ (prefixWord ++ tailWord_789933).sum := by decide
  have hdescent : baseEnd_789933 < baseStart_789933 := by decide
  rcases family_descends (prefixWord ++ tailWord_789933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789937 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 2]
def baseStart_789937 : Nat := 118140960795 + 789937 * 2 ^ 59
def prefixEnd_789937 : Nat := 4983230072969 + 3 ^ 40 * 789937 * 2
def baseEnd_789937 : Nat := 360548771351805423604135

theorem tailTrace_789937 : CollatzResearch.WordTrace tailWord_789937 prefixEnd_789937 360548771351805423604135 := by
  unfold tailWord_789937
  simp only [CollatzResearch.WordTrace]
  refine ⟨28811369339200634343936065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19207579559467089562624043 28811369339200634343936065)
  ·
    refine ⟨21608527004400475757952049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28811369339200634343936065 21608527004400475757952049)
    ·
      refine ⟨16206395253300356818464037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21608527004400475757952049 16206395253300356818464037)
      ·
        refine ⟨3038699109993816903462007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16206395253300356818464037 3038699109993816903462007)
        ·
          refine ⟨4558048664990725355193011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038699109993816903462007 4558048664990725355193011)
          ·
            refine ⟨6837072997486088032789517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558048664990725355193011 6837072997486088032789517)
            ·
              refine ⟨2563902374057283012296069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6837072997486088032789517 2563902374057283012296069)
              ·
                refine ⟨480731695135740564805513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2563902374057283012296069 480731695135740564805513)
                ·
                  refine ⟨360548771351805423604135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480731695135740564805513 360548771351805423604135)
                  ·
                    rfl

theorem cell20_789937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_789937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789937 prefixEnd_789937 := by exact prefixLift 789937
  have htrace : WordTrace (prefixWord ++ tailWord_789937) baseStart_789937 baseEnd_789937 := by
    simpa [prefixWord, tailWord_789937, baseEnd_789937] using wordTrace_append hprefix tailTrace_789937
  have hstable : (prefixWord ++ tailWord_789937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789937).length < 2 ^ (prefixWord ++ tailWord_789937).sum := by decide
  have hdescent : baseEnd_789937 < baseStart_789937 := by decide
  rcases family_descends (prefixWord ++ tailWord_789937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789989 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_789989 : Nat := 118140960795 + 789989 * 2 ^ 59
def prefixEnd_789989 : Nat := 4983230072969 + 3 ^ 40 * 789989 * 2
def baseEnd_789989 : Nat := 360572505568724353870589

theorem tailTrace_789989 : CollatzResearch.WordTrace tailWord_789989 prefixEnd_789989 360572505568724353870589 := by
  unfold tailWord_789989
  simp only [CollatzResearch.WordTrace]
  refine ⟨28813265935012247224829021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19208843956674831483219347 28813265935012247224829021)
  ·
    refine ⟨10804974725629592709310883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28813265935012247224829021 10804974725629592709310883)
    ·
      refine ⟨16207462088444389063966325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10804974725629592709310883 16207462088444389063966325)
      ·
        refine ⟨1519449570791661474746843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16207462088444389063966325 1519449570791661474746843)
        ·
          refine ⟨2279174356187492212120265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519449570791661474746843 2279174356187492212120265)
          ·
            refine ⟨1709380767140619159090199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2279174356187492212120265 1709380767140619159090199)
            ·
              refine ⟨2564071150710928738635299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709380767140619159090199 2564071150710928738635299)
              ·
                refine ⟨3846106726066393107952949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564071150710928738635299 3846106726066393107952949)
                ·
                  refine ⟨360572505568724353870589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3846106726066393107952949 360572505568724353870589)
                  ·
                    rfl

theorem cell20_789989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_789989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_789989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_789989 prefixEnd_789989 := by exact prefixLift 789989
  have htrace : WordTrace (prefixWord ++ tailWord_789989) baseStart_789989 baseEnd_789989 := by
    simpa [prefixWord, tailWord_789989, baseEnd_789989] using wordTrace_append hprefix tailTrace_789989
  have hstable : (prefixWord ++ tailWord_789989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789989).length < 2 ^ (prefixWord ++ tailWord_789989).sum := by decide
  have hdescent : baseEnd_789989 < baseStart_789989 := by decide
  rcases family_descends (prefixWord ++ tailWord_789989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790020 : List Nat := [2, 3, 2, 3, 2, 1, 1, 6]
def baseStart_790020 : Nat := 118140960795 + 790020 * 2 ^ 59
def prefixEnd_790020 : Nat := 4983230072969 + 3 ^ 40 * 790020 * 2
def baseEnd_790020 : Nat := 120195551604475341279043

theorem tailTrace_790020 : CollatzResearch.WordTrace tailWord_790020 prefixEnd_790020 120195551604475341279043 := by
  unfold tailWord_790020
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407198298949969759603757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19209597731933293012805009 14407198298949969759603757)
  ·
    refine ⟨5402699362106238659851409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14407198298949969759603757 5402699362106238659851409)
    ·
      refine ⟨4052024521579678994888557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5402699362106238659851409 4052024521579678994888557)
      ·
        refine ⟨1519509195592379623083209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4052024521579678994888557 1519509195592379623083209)
        ·
          refine ⟨1139631896694284717312407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519509195592379623083209 1139631896694284717312407)
          ·
            refine ⟨1709447845041427075968611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139631896694284717312407 1709447845041427075968611)
            ·
              refine ⟨2564171767562140613952917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709447845041427075968611 2564171767562140613952917)
              ·
                refine ⟨120195551604475341279043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2564171767562140613952917 120195551604475341279043)
                ·
                  rfl

theorem cell20_790020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_790020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790020 prefixEnd_790020 := by exact prefixLift 790020
  have htrace : WordTrace (prefixWord ++ tailWord_790020) baseStart_790020 baseEnd_790020 := by
    simpa [prefixWord, tailWord_790020, baseEnd_790020] using wordTrace_append hprefix tailTrace_790020
  have hstable : (prefixWord ++ tailWord_790020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790020).length < 2 ^ (prefixWord ++ tailWord_790020).sum := by decide
  have hdescent : baseEnd_790020 < baseStart_790020 := by decide
  rcases family_descends (prefixWord ++ tailWord_790020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790022 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_790022 : Nat := 118140960795 + 790022 * 2 ^ 59
def prefixEnd_790022 : Nat := 4983230072969 + 3 ^ 40 * 790022 * 2
def baseEnd_790022 : Nat := 360587567667922905770455

theorem tailTrace_790022 : CollatzResearch.WordTrace tailWord_790022 prefixEnd_790022 360587567667922905770455 := by
  unfold tailWord_790022
  simp only [CollatzResearch.WordTrace]
  refine ⟨900452173246646683149385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19209646362595129240520213 900452173246646683149385)
  ·
    refine ⟨675339129934985012362039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 900452173246646683149385 675339129934985012362039)
    ·
      refine ⟨1013008694902477518543059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675339129934985012362039 1013008694902477518543059)
      ·
        refine ⟨1519513042353716277814589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013008694902477518543059 1519513042353716277814589)
        ·
          refine ⟨569817390882643604180471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1519513042353716277814589 569817390882643604180471)
          ·
            refine ⟨854726086323965406270707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569817390882643604180471 854726086323965406270707)
            ·
              refine ⟨1282089129485948109406061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854726086323965406270707 1282089129485948109406061)
              ·
                refine ⟨480783423557230541027273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282089129485948109406061 480783423557230541027273)
                ·
                  refine ⟨360587567667922905770455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480783423557230541027273 360587567667922905770455)
                  ·
                    rfl

theorem cell20_790022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_790022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790022 prefixEnd_790022 := by exact prefixLift 790022
  have htrace : WordTrace (prefixWord ++ tailWord_790022) baseStart_790022 baseEnd_790022 := by
    simpa [prefixWord, tailWord_790022, baseEnd_790022] using wordTrace_append hprefix tailTrace_790022
  have hstable : (prefixWord ++ tailWord_790022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790022).length < 2 ^ (prefixWord ++ tailWord_790022).sum := by decide
  have hdescent : baseEnd_790022 < baseStart_790022 := by decide
  rcases family_descends (prefixWord ++ tailWord_790022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790051 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 4]
def baseStart_790051 : Nat := 118140960795 + 790051 * 2 ^ 59
def prefixEnd_790051 : Nat := 4983230072969 + 3 ^ 40 * 790051 * 2
def baseEnd_790051 : Nat := 360600804058127693803669

theorem tailTrace_790051 : CollatzResearch.WordTrace tailWord_790051 prefixEnd_790051 360600804058127693803669 := by
  unfold tailWord_790051
  simp only [CollatzResearch.WordTrace]
  refine ⟨28815527260787631813586007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19210351507191754542390671 28815527260787631813586007)
  ·
    refine ⟨43223290891181447720379011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28815527260787631813586007 43223290891181447720379011)
    ·
      refine ⟨64834936336772171580568517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43223290891181447720379011 64834936336772171580568517)
      ·
        refine ⟨12156550563144782171356597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64834936336772171580568517 12156550563144782171356597)
        ·
          refine ⟨1139676615294823328564681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12156550563144782171356597 1139676615294823328564681)
          ·
            refine ⟨854757461471117496423511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139676615294823328564681 854757461471117496423511)
            ·
              refine ⟨1282136192206676244635267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854757461471117496423511 1282136192206676244635267)
              ·
                refine ⟨1923204288310014366952901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282136192206676244635267 1923204288310014366952901)
                ·
                  refine ⟨360600804058127693803669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923204288310014366952901 360600804058127693803669)
                  ·
                    rfl

theorem cell20_790051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_790051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790051 prefixEnd_790051 := by exact prefixLift 790051
  have htrace : WordTrace (prefixWord ++ tailWord_790051) baseStart_790051 baseEnd_790051 := by
    simpa [prefixWord, tailWord_790051, baseEnd_790051] using wordTrace_append hprefix tailTrace_790051
  have hstable : (prefixWord ++ tailWord_790051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790051).length < 2 ^ (prefixWord ++ tailWord_790051).sum := by decide
  have hdescent : baseEnd_790051 < baseStart_790051 := by decide
  rcases family_descends (prefixWord ++ tailWord_790051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790102 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_790102 : Nat := 118140960795 + 790102 * 2 ^ 59
def prefixEnd_790102 : Nat := 4983230072969 + 3 ^ 40 * 790102 * 2
def baseEnd_790102 : Nat := 360624081847798183103461

theorem tailTrace_790102 : CollatzResearch.WordTrace tailWord_790102 prefixEnd_790102 360624081847798183103461 := by
  unfold tailWord_790102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801086711475179220230785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19211591589068578349128373 1801086711475179220230785)
  ·
    refine ⟨1350815033606384415173089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1801086711475179220230785 1350815033606384415173089)
    ·
      refine ⟨1013111275204788311379817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1350815033606384415173089 1013111275204788311379817)
      ·
        refine ⟨759833456403591233534863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1013111275204788311379817 759833456403591233534863)
        ·
          refine ⟨1139750184605386850302295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759833456403591233534863 1139750184605386850302295)
          ·
            refine ⟨1709625276908080275453443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139750184605386850302295 1709625276908080275453443)
            ·
              refine ⟨2564437915362120413180165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709625276908080275453443 2564437915362120413180165)
              ·
                refine ⟨480832109130397577471281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2564437915362120413180165 480832109130397577471281)
                ·
                  refine ⟨360624081847798183103461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480832109130397577471281 360624081847798183103461)
                  ·
                    rfl

theorem cell20_790102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_790102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790102 prefixEnd_790102 := by exact prefixLift 790102
  have htrace : WordTrace (prefixWord ++ tailWord_790102) baseStart_790102 baseEnd_790102 := by
    simpa [prefixWord, tailWord_790102, baseEnd_790102] using wordTrace_append hprefix tailTrace_790102
  have hstable : (prefixWord ++ tailWord_790102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790102).length < 2 ^ (prefixWord ++ tailWord_790102).sum := by decide
  have hdescent : baseEnd_790102 < baseStart_790102 := by decide
  rcases family_descends (prefixWord ++ tailWord_790102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790103 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_790103 : Nat := 118140960795 + 790103 * 2 ^ 59
def prefixEnd_790103 : Nat := 4983230072969 + 3 ^ 40 * 790103 * 2
def baseEnd_790103 : Nat := 360624538275046624070123

theorem tailTrace_790103 : CollatzResearch.WordTrace tailWord_790103 prefixEnd_790103 360624538275046624070123 := by
  unfold tailWord_790103
  simp only [CollatzResearch.WordTrace]
  refine ⟨28817423856599244694478963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19211615904399496462985975 28817423856599244694478963)
  ·
    refine ⟨43226135784898867041718445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28817423856599244694478963 43226135784898867041718445)
    ·
      refine ⟨16209800919337075140644417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43226135784898867041718445 16209800919337075140644417)
      ·
        refine ⟨12157350689502806355483313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16209800919337075140644417 12157350689502806355483313)
        ·
          refine ⟨9118013017127104766612485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12157350689502806355483313 9118013017127104766612485)
          ·
            refine ⟨1709627440711332143739841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9118013017127104766612485 1709627440711332143739841)
            ·
              refine ⟨1282220580533499107804881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709627440711332143739841 1282220580533499107804881)
              ·
                refine ⟨961665435400124330853661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282220580533499107804881 961665435400124330853661)
                ·
                  refine ⟨360624538275046624070123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961665435400124330853661 360624538275046624070123)
                  ·
                    rfl

theorem cell20_790103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_790103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790103 prefixEnd_790103 := by exact prefixLift 790103
  have htrace : WordTrace (prefixWord ++ tailWord_790103) baseStart_790103 baseEnd_790103 := by
    simpa [prefixWord, tailWord_790103, baseEnd_790103] using wordTrace_append hprefix tailTrace_790103
  have hstable : (prefixWord ++ tailWord_790103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790103).length < 2 ^ (prefixWord ++ tailWord_790103).sum := by decide
  have hdescent : baseEnd_790103 < baseStart_790103 := by decide
  rcases family_descends (prefixWord ++ tailWord_790103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790117 : List Nat := [1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_790117 : Nat := 118140960795 + 790117 * 2 ^ 59
def prefixEnd_790117 : Nat := 4983230072969 + 3 ^ 40 * 790117 * 2
def baseEnd_790117 : Nat := 120210309418841599201133

theorem tailTrace_790117 : CollatzResearch.WordTrace tailWord_790117 prefixEnd_790117 120210309418841599201133 := by
  unfold tailWord_790117
  simp only [CollatzResearch.WordTrace]
  refine ⟨28817934478548525085488605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19211956319032350056992403 28817934478548525085488605)
  ·
    refine ⟨10806725429455696907058227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28817934478548525085488605 10806725429455696907058227)
    ·
      refine ⟨16210088144183545360587341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806725429455696907058227 16210088144183545360587341)
      ·
        refine ⟨6078783054068829510220253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16210088144183545360587341 6078783054068829510220253)
        ·
          refine ⟨2279543645275811066332595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6078783054068829510220253 2279543645275811066332595)
          ·
            refine ⟨3419315467913716599498893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279543645275811066332595 3419315467913716599498893)
            ·
              refine ⟨1282243300467643724812085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3419315467913716599498893 1282243300467643724812085)
              ·
                refine ⟨120210309418841599201133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1282243300467643724812085 120210309418841599201133)
                ·
                  rfl

theorem cell20_790117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_790117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790117 prefixEnd_790117 := by exact prefixLift 790117
  have htrace : WordTrace (prefixWord ++ tailWord_790117) baseStart_790117 baseEnd_790117 := by
    simpa [prefixWord, tailWord_790117, baseEnd_790117] using wordTrace_append hprefix tailTrace_790117
  have hstable : (prefixWord ++ tailWord_790117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790117).length < 2 ^ (prefixWord ++ tailWord_790117).sum := by decide
  have hdescent : baseEnd_790117 < baseStart_790117 := by decide
  rcases family_descends (prefixWord ++ tailWord_790117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790158 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_790158 : Nat := 118140960795 + 790158 * 2 ^ 59
def prefixEnd_790158 : Nat := 4983230072969 + 3 ^ 40 * 790158 * 2
def baseEnd_790158 : Nat := 360649641773710877236565

theorem tailTrace_790158 : CollatzResearch.WordTrace tailWord_790158 prefixEnd_790158 360649641773710877236565 := by
  unfold tailWord_790158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602428733924998635966391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19212953247599992725154085 3602428733924998635966391)
  ·
    refine ⟨5403643100887497953949587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3602428733924998635966391 5403643100887497953949587)
    ·
      refine ⟨8105464651331246930924381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5403643100887497953949587 8105464651331246930924381)
      ·
        refine ⟨3039549244249217599096643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8105464651331246930924381 3039549244249217599096643)
        ·
          refine ⟨4559323866373826398644965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039549244249217599096643 4559323866373826398644965)
          ·
            refine ⟨854873224945092449745931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4559323866373826398644965 854873224945092449745931)
            ·
              refine ⟨1282309837417638674618897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854873224945092449745931 1282309837417638674618897)
              ·
                refine ⟨961732378063229005964173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282309837417638674618897 961732378063229005964173)
                ·
                  refine ⟨360649641773710877236565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961732378063229005964173 360649641773710877236565)
                  ·
                    rfl

theorem cell20_790158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_790158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790158 prefixEnd_790158 := by exact prefixLift 790158
  have htrace : WordTrace (prefixWord ++ tailWord_790158) baseStart_790158 baseEnd_790158 := by
    simpa [prefixWord, tailWord_790158, baseEnd_790158] using wordTrace_append hprefix tailTrace_790158
  have hstable : (prefixWord ++ tailWord_790158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790158).length < 2 ^ (prefixWord ++ tailWord_790158).sum := by decide
  have hdescent : baseEnd_790158 < baseStart_790158 := by decide
  rcases family_descends (prefixWord ++ tailWord_790158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790175 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 3]
def baseStart_790175 : Nat := 118140960795 + 790175 * 2 ^ 59
def prefixEnd_790175 : Nat := 4983230072969 + 3 ^ 40 * 790175 * 2
def baseEnd_790175 : Nat := 360657401036934373669829

theorem tailTrace_790175 : CollatzResearch.WordTrace tailWord_790175 prefixEnd_790175 360657401036934373669829 := by
  unfold tailWord_790175
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820049912338400991099979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19213366608225600660733319 28820049912338400991099979)
  ·
    refine ⟨43230074868507601486649969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28820049912338400991099979 43230074868507601486649969)
    ·
      refine ⟨32422556151380701114987477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43230074868507601486649969 32422556151380701114987477)
      ·
        refine ⟨759903659797985182382519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32422556151380701114987477 759903659797985182382519)
        ·
          refine ⟨1139855489696977773573779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759903659797985182382519 1139855489696977773573779)
          ·
            refine ⟨1709783234545466660360669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139855489696977773573779 1709783234545466660360669)
            ·
              refine ⟨641168712954549997635251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1709783234545466660360669 641168712954549997635251)
              ·
                refine ⟨961753069431824996452877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641168712954549997635251 961753069431824996452877)
                ·
                  refine ⟨360657401036934373669829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961753069431824996452877 360657401036934373669829)
                  ·
                    rfl

theorem cell20_790175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_790175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790175 prefixEnd_790175 := by exact prefixLift 790175
  have htrace : WordTrace (prefixWord ++ tailWord_790175) baseStart_790175 baseEnd_790175 := by
    simpa [prefixWord, tailWord_790175, baseEnd_790175] using wordTrace_append hprefix tailTrace_790175
  have hstable : (prefixWord ++ tailWord_790175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790175).length < 2 ^ (prefixWord ++ tailWord_790175).sum := by decide
  have hdescent : baseEnd_790175 < baseStart_790175 := by decide
  rcases family_descends (prefixWord ++ tailWord_790175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790179 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 3]
def baseStart_790179 : Nat := 118140960795 + 790179 * 2 ^ 59
def prefixEnd_790179 : Nat := 4983230072969 + 3 ^ 40 * 790179 * 2
def baseEnd_790179 : Nat := 360659226745928137536479

theorem tailTrace_790179 : CollatzResearch.WordTrace tailWord_790179 prefixEnd_790179 360659226745928137536479 := by
  unfold tailWord_790179
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820195804323909674245591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19213463869549273116163727 28820195804323909674245591)
  ·
    refine ⟨43230293706485864511368387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28820195804323909674245591 43230293706485864511368387)
    ·
      refine ⟨64845440559728796767052581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43230293706485864511368387 64845440559728796767052581)
      ·
        refine ⟨12158520104949149393822359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64845440559728796767052581 12158520104949149393822359)
        ·
          refine ⟨18237780157423724090733539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12158520104949149393822359 18237780157423724090733539)
          ·
            refine ⟨27356670236135586136100309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18237780157423724090733539 27356670236135586136100309)
            ·
              refine ⟨641171958659427800064851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27356670236135586136100309 641171958659427800064851)
              ·
                refine ⟨961757937989141700097277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641171958659427800064851 961757937989141700097277)
                ·
                  refine ⟨360659226745928137536479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961757937989141700097277 360659226745928137536479)
                  ·
                    rfl

theorem cell20_790179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_790179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790179 prefixEnd_790179 := by exact prefixLift 790179
  have htrace : WordTrace (prefixWord ++ tailWord_790179) baseStart_790179 baseEnd_790179 := by
    simpa [prefixWord, tailWord_790179, baseEnd_790179] using wordTrace_append hprefix tailTrace_790179
  have hstable : (prefixWord ++ tailWord_790179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790179).length < 2 ^ (prefixWord ++ tailWord_790179).sum := by decide
  have hdescent : baseEnd_790179 < baseStart_790179 := by decide
  rcases family_descends (prefixWord ++ tailWord_790179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790220 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 4]
def baseStart_790220 : Nat := 118140960795 + 790220 * 2 ^ 59
def prefixEnd_790220 : Nat := 4983230072969 + 3 ^ 40 * 790220 * 2
def baseEnd_790220 : Nat := 360677940263114217169645

theorem tailTrace_790220 : CollatzResearch.WordTrace tailWord_790220 prefixEnd_790220 360677940263114217169645 := by
  unfold tailWord_790220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14410845598587686838244057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19214460798116915784325409 14410845598587686838244057)
  ·
    refine ⟨10808134198940765128683043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14410845598587686838244057 10808134198940765128683043)
    ·
      refine ⟨16212201298411147693024565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808134198940765128683043 16212201298411147693024565)
      ·
        refine ⟨1519893871726045096221053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16212201298411147693024565 1519893871726045096221053)
        ·
          refine ⟨569960201897266911082895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1519893871726045096221053 569960201897266911082895)
          ·
            refine ⟨854940302845900366624343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569960201897266911082895 854940302845900366624343)
            ·
              refine ⟨1282410454268850549936515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854940302845900366624343 1282410454268850549936515)
              ·
                refine ⟨1923615681403275824904773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282410454268850549936515 1923615681403275824904773)
                ·
                  refine ⟨360677940263114217169645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923615681403275824904773 360677940263114217169645)
                  ·
                    rfl

theorem cell20_790220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_790220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790220 prefixEnd_790220 := by exact prefixLift 790220
  have htrace : WordTrace (prefixWord ++ tailWord_790220) baseStart_790220 baseEnd_790220 := by
    simpa [prefixWord, tailWord_790220, baseEnd_790220] using wordTrace_append hprefix tailTrace_790220
  have hstable : (prefixWord ++ tailWord_790220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790220).length < 2 ^ (prefixWord ++ tailWord_790220).sum := by decide
  have hdescent : baseEnd_790220 < baseStart_790220 := by decide
  rcases family_descends (prefixWord ++ tailWord_790220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790234 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_790234 : Nat := 118140960795 + 790234 * 2 ^ 59
def prefixEnd_790234 : Nat := 4983230072969 + 3 ^ 40 * 790234 * 2
def baseEnd_790234 : Nat := 360684330244592390702921

theorem tailTrace_790234 : CollatzResearch.WordTrace tailWord_790234 prefixEnd_790234 360684330244592390702921 := by
  unfold tailWord_790234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205550454781163516874439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19214801212749769378331837 7205550454781163516874439)
  ·
    refine ⟨10808325682171745275311659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205550454781163516874439 10808325682171745275311659)
    ·
      refine ⟨16212488523257617912967489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808325682171745275311659 16212488523257617912967489)
      ·
        refine ⟨12159366392443213434725617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16212488523257617912967489 12159366392443213434725617)
        ·
          refine ⟨9119524794332410076044213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12159366392443213434725617 9119524794332410076044213)
          ·
            refine ⟨854955449468663444629145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9119524794332410076044213 854955449468663444629145)
            ·
              refine ⟨641216587101497583471859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854955449468663444629145 641216587101497583471859)
              ·
                refine ⟨961824880652246375207789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641216587101497583471859 961824880652246375207789)
                ·
                  refine ⟨360684330244592390702921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961824880652246375207789 360684330244592390702921)
                  ·
                    rfl

theorem cell20_790234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_790234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790234 prefixEnd_790234 := by exact prefixLift 790234
  have htrace : WordTrace (prefixWord ++ tailWord_790234) baseStart_790234 baseEnd_790234 := by
    simpa [prefixWord, tailWord_790234, baseEnd_790234] using wordTrace_append hprefix tailTrace_790234
  have hstable : (prefixWord ++ tailWord_790234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790234).length < 2 ^ (prefixWord ++ tailWord_790234).sum := by decide
  have hdescent : baseEnd_790234 < baseStart_790234 := by decide
  rcases family_descends (prefixWord ++ tailWord_790234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790245 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_790245 : Nat := 118140960795 + 790245 * 2 ^ 59
def prefixEnd_790245 : Nat := 4983230072969 + 3 ^ 40 * 790245 * 2
def baseEnd_790245 : Nat := 360689350944325241336209

theorem tailTrace_790245 : CollatzResearch.WordTrace tailWord_790245 prefixEnd_790245 360689350944325241336209 := by
  unfold tailWord_790245
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822603022084802946148189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19215068681389868630765459 28822603022084802946148189)
  ·
    refine ⟨10808476133281801104805571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28822603022084802946148189 10808476133281801104805571)
    ·
      refine ⟨16212714199922701657208357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808476133281801104805571 16212714199922701657208357)
      ·
        refine ⟨3039883912485506560726567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16212714199922701657208357 3039883912485506560726567)
        ·
          refine ⟨4559825868728259841089851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039883912485506560726567 4559825868728259841089851)
          ·
            refine ⟨6839738803092389761634777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559825868728259841089851 6839738803092389761634777)
            ·
              refine ⟨5129804102319292321226083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6839738803092389761634777 5129804102319292321226083)
              ·
                refine ⟨7694706153478938481839125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129804102319292321226083 7694706153478938481839125)
                ·
                  refine ⟨360689350944325241336209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7694706153478938481839125 360689350944325241336209)
                  ·
                    rfl

theorem cell20_790245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_790245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790245 prefixEnd_790245 := by exact prefixLift 790245
  have htrace : WordTrace (prefixWord ++ tailWord_790245) baseStart_790245 baseEnd_790245 := by
    simpa [prefixWord, tailWord_790245, baseEnd_790245] using wordTrace_append hprefix tailTrace_790245
  have hstable : (prefixWord ++ tailWord_790245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790245).length < 2 ^ (prefixWord ++ tailWord_790245).sum := by decide
  have hdescent : baseEnd_790245 < baseStart_790245 := by decide
  rcases family_descends (prefixWord ++ tailWord_790245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790252 : List Nat := [2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_790252 : Nat := 118140960795 + 790252 * 2 ^ 59
def prefixEnd_790252 : Nat := 4983230072969 + 3 ^ 40 * 790252 * 2
def baseEnd_790252 : Nat := 120230848645021442700949

theorem tailTrace_790252 : CollatzResearch.WordTrace tailWord_790252 prefixEnd_790252 120230848645021442700949 := by
  unfold tailWord_790252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14411429166529721570826505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19215238888706295427768673 14411429166529721570826505)
  ·
    refine ⟨10808571874897291178119879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14411429166529721570826505 10808571874897291178119879)
    ·
      refine ⟨16212857812345936767179819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808571874897291178119879 16212857812345936767179819)
      ·
        refine ⟨24319286718518905150769729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16212857812345936767179819 24319286718518905150769729)
        ·
          refine ⟨18239465038889178863077297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24319286718518905150769729 18239465038889178863077297)
          ·
            refine ⟨13679598779166884147307973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18239465038889178863077297 13679598779166884147307973)
            ·
              refine ⟨2564924771093790777620245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13679598779166884147307973 2564924771093790777620245)
              ·
                refine ⟨120230848645021442700949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2564924771093790777620245 120230848645021442700949)
                ·
                  rfl

theorem cell20_790252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_790252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790252 prefixEnd_790252 := by exact prefixLift 790252
  have htrace : WordTrace (prefixWord ++ tailWord_790252) baseStart_790252 baseEnd_790252 := by
    simpa [prefixWord, tailWord_790252, baseEnd_790252] using wordTrace_append hprefix tailTrace_790252
  have hstable : (prefixWord ++ tailWord_790252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790252).length < 2 ^ (prefixWord ++ tailWord_790252).sum := by decide
  have hdescent : baseEnd_790252 < baseStart_790252 := by decide
  rcases family_descends (prefixWord ++ tailWord_790252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790259 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_790259 : Nat := 118140960795 + 790259 * 2 ^ 59
def prefixEnd_790259 : Nat := 4983230072969 + 3 ^ 40 * 790259 * 2
def baseEnd_790259 : Nat := 360695740925803414869485

theorem tailTrace_790259 : CollatzResearch.WordTrace tailWord_790259 prefixEnd_790259 360695740925803414869485 := by
  unfold tailWord_790259
  simp only [CollatzResearch.WordTrace]
  refine ⟨28823113644034083337157831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19215409096022722224771887 28823113644034083337157831)
  ·
    refine ⟨43234670466051125005736747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28823113644034083337157831 43234670466051125005736747)
    ·
      refine ⟨64852005699076687508605121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43234670466051125005736747 64852005699076687508605121)
      ·
        refine ⟨48639004274307515631453841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64852005699076687508605121 48639004274307515631453841)
        ·
          refine ⟨36479253205730636723590381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48639004274307515631453841 36479253205730636723590381)
          ·
            refine ⟨13679719952148988771346393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36479253205730636723590381 13679719952148988771346393)
            ·
              refine ⟨10259789964111741578509795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13679719952148988771346393 10259789964111741578509795)
              ·
                refine ⟨15389684946167612367764693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259789964111741578509795 15389684946167612367764693)
                ·
                  refine ⟨360695740925803414869485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15389684946167612367764693 360695740925803414869485)
                  ·
                    rfl

theorem cell20_790259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_790259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790259 prefixEnd_790259 := by exact prefixLift 790259
  have htrace : WordTrace (prefixWord ++ tailWord_790259) baseStart_790259 baseEnd_790259 := by
    simpa [prefixWord, tailWord_790259, baseEnd_790259] using wordTrace_append hprefix tailTrace_790259
  have hstable : (prefixWord ++ tailWord_790259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790259).length < 2 ^ (prefixWord ++ tailWord_790259).sum := by decide
  have hdescent : baseEnd_790259 < baseStart_790259 := by decide
  rcases family_descends (prefixWord ++ tailWord_790259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790278 : List Nat := [6, 2, 2, 1, 1, 2, 1, 5]
def baseStart_790278 : Nat := 118140960795 + 790278 * 2 ^ 59
def prefixEnd_790278 : Nat := 4983230072969 + 3 ^ 40 * 790278 * 2
def baseEnd_790278 : Nat := 120234804347841264412025

theorem tailTrace_790278 : CollatzResearch.WordTrace tailWord_790278 prefixEnd_790278 120234804347841264412025 := by
  unfold tailWord_790278
  simp only [CollatzResearch.WordTrace]
  refine ⟨900743957217664049440609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19215871087310166388066325 900743957217664049440609)
  ·
    refine ⟨675557967913248037080457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 900743957217664049440609 675557967913248037080457)
    ·
      refine ⟨506668475934936027810343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675557967913248037080457 506668475934936027810343)
      ·
        refine ⟨760002713902404041715515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506668475934936027810343 760002713902404041715515)
        ·
          refine ⟨1140004070853606062573273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760002713902404041715515 1140004070853606062573273)
          ·
            refine ⟨855003053140204546929955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140004070853606062573273 855003053140204546929955)
            ·
              refine ⟨1282504579710306820394933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855003053140204546929955 1282504579710306820394933)
              ·
                refine ⟨120234804347841264412025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1282504579710306820394933 120234804347841264412025)
                ·
                  rfl

theorem cell20_790278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_790278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790278 prefixEnd_790278 := by exact prefixLift 790278
  have htrace : WordTrace (prefixWord ++ tailWord_790278) baseStart_790278 baseEnd_790278 := by
    simpa [prefixWord, tailWord_790278, baseEnd_790278] using wordTrace_append hprefix tailTrace_790278
  have hstable : (prefixWord ++ tailWord_790278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790278).length < 2 ^ (prefixWord ++ tailWord_790278).sum := by decide
  have hdescent : baseEnd_790278 < baseStart_790278 := by decide
  rcases family_descends (prefixWord ++ tailWord_790278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790328 : List Nat := [2, 1, 2, 1, 3, 4, 7]
def baseStart_790328 : Nat := 118140960795 + 790328 * 2 ^ 59
def prefixEnd_790328 : Nat := 4983230072969 + 3 ^ 40 * 790328 * 2
def baseEnd_790328 : Nat := 40080803822882871285467

theorem tailTrace_790328 : CollatzResearch.WordTrace tailWord_790328 prefixEnd_790328 40080803822882871285467 := by
  unfold tailWord_790328
  simp only [CollatzResearch.WordTrace]
  refine ⟨14412815140392054060709819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19217086853856072080946425 14412815140392054060709819)
  ·
    refine ⟨21619222710588081091064729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14412815140392054060709819 21619222710588081091064729)
    ·
      refine ⟨16214417032941060818298547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21619222710588081091064729 16214417032941060818298547)
      ·
        refine ⟨24321625549411591227447821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16214417032941060818298547 24321625549411591227447821)
        ·
          refine ⟨9120609581029346710292933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24321625549411591227447821 9120609581029346710292933)
          ·
            refine ⟨1710114296443002508179925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9120609581029346710292933 1710114296443002508179925)
            ·
              refine ⟨40080803822882871285467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1710114296443002508179925 40080803822882871285467)
              ·
                rfl

theorem cell20_790328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_790328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790328 prefixEnd_790328 := by exact prefixLift 790328
  have htrace : WordTrace (prefixWord ++ tailWord_790328) baseStart_790328 baseEnd_790328 := by
    simpa [prefixWord, tailWord_790328, baseEnd_790328] using wordTrace_append hprefix tailTrace_790328
  have hstable : (prefixWord ++ tailWord_790328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790328).length < 2 ^ (prefixWord ++ tailWord_790328).sum := by decide
  have hdescent : baseEnd_790328 < baseStart_790328 := by decide
  rcases family_descends (prefixWord ++ tailWord_790328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790348 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_790348 : Nat := 118140960795 + 790348 * 2 ^ 59
def prefixEnd_790348 : Nat := 4983230072969 + 3 ^ 40 * 790348 * 2
def baseEnd_790348 : Nat := 360736362950914660902455

theorem tailTrace_790348 : CollatzResearch.WordTrace tailWord_790348 prefixEnd_790348 360736362950914660902455 := by
  unfold tailWord_790348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413179870355825768573849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19217573160474434358098465 14413179870355825768573849)
  ·
    refine ⟨10809884902766869326430387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14413179870355825768573849 10809884902766869326430387)
    ·
      refine ⟨16214827354150303989645581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10809884902766869326430387 16214827354150303989645581)
      ·
        refine ⟨6080560257806363996117093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16214827354150303989645581 6080560257806363996117093)
        ·
          refine ⟨1140105048338693249271955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6080560257806363996117093 1140105048338693249271955)
          ·
            refine ⟨1710157572508039873907933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140105048338693249271955 1710157572508039873907933)
            ·
              refine ⟨641309089690514952715475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1710157572508039873907933 641309089690514952715475)
              ·
                refine ⟨961963634535772429073213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641309089690514952715475 961963634535772429073213)
                ·
                  refine ⟨360736362950914660902455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961963634535772429073213 360736362950914660902455)
                  ·
                    rfl

theorem cell20_790348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_790348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790348 prefixEnd_790348 := by exact prefixLift 790348
  have htrace : WordTrace (prefixWord ++ tailWord_790348) baseStart_790348 baseEnd_790348 := by
    simpa [prefixWord, tailWord_790348, baseEnd_790348] using wordTrace_append hprefix tailTrace_790348
  have hstable : (prefixWord ++ tailWord_790348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790348).length < 2 ^ (prefixWord ++ tailWord_790348).sum := by decide
  have hdescent : baseEnd_790348 < baseStart_790348 := by decide
  rcases family_descends (prefixWord ++ tailWord_790348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790372 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 2]
def baseStart_790372 : Nat := 118140960795 + 790372 * 2 ^ 59
def prefixEnd_790372 : Nat := 4983230072969 + 3 ^ 40 * 790372 * 2
def baseEnd_790372 : Nat := 360747317204877244102357

theorem tailTrace_790372 : CollatzResearch.WordTrace tailWord_790372 prefixEnd_790372 360747317204877244102357 := by
  unfold tailWord_790372
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413617546312351818010685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19218156728416469090680913 14413617546312351818010685)
  ·
    refine ⟨5405106579867131931754007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14413617546312351818010685 5405106579867131931754007)
    ·
      refine ⟨8107659869800697897631011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405106579867131931754007 8107659869800697897631011)
      ·
        refine ⟨12161489804701046846446517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8107659869800697897631011 12161489804701046846446517)
        ·
          refine ⟨1140139669190723141854361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12161489804701046846446517 1140139669190723141854361)
          ·
            refine ⟨855104751893042356390771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140139669190723141854361 855104751893042356390771)
            ·
              refine ⟨1282657127839563534586157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855104751893042356390771 1282657127839563534586157)
              ·
                refine ⟨480996422939836325469809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282657127839563534586157 480996422939836325469809)
                ·
                  refine ⟨360747317204877244102357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480996422939836325469809 360747317204877244102357)
                  ·
                    rfl

theorem cell20_790372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_790372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790372 prefixEnd_790372 := by exact prefixLift 790372
  have htrace : WordTrace (prefixWord ++ tailWord_790372) baseStart_790372 baseEnd_790372 := by
    simpa [prefixWord, tailWord_790372, baseEnd_790372] using wordTrace_append hprefix tailTrace_790372
  have hstable : (prefixWord ++ tailWord_790372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790372).length < 2 ^ (prefixWord ++ tailWord_790372).sum := by decide
  have hdescent : baseEnd_790372 < baseStart_790372 := by decide
  rcases family_descends (prefixWord ++ tailWord_790372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790393 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 2]
def baseStart_790393 : Nat := 118140960795 + 790393 * 2 ^ 59
def prefixEnd_790393 : Nat := 4983230072969 + 3 ^ 40 * 790393 * 2
def baseEnd_790393 : Nat := 360756902177094504402271

theorem tailTrace_790393 : CollatzResearch.WordTrace tailWord_790393 prefixEnd_790393 360756902177094504402271 := by
  unfold tailWord_790393
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828001025548624222535833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19218667350365749481690555 28828001025548624222535833)
  ·
    refine ⟨21621000769161468166901875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28828001025548624222535833 21621000769161468166901875)
    ·
      refine ⟨32431501153742202250352813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21621000769161468166901875 32431501153742202250352813)
      ·
        refine ⟨12161812932653325843882305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32431501153742202250352813 12161812932653325843882305)
        ·
          refine ⟨9121359699489994382911729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12161812932653325843882305 9121359699489994382911729)
          ·
            refine ⟨6841019774617495787183797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9121359699489994382911729 6841019774617495787183797)
            ·
              refine ⟨641345603870390230048481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6841019774617495787183797 641345603870390230048481)
              ·
                refine ⟨481009202902792672536361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641345603870390230048481 481009202902792672536361)
                ·
                  refine ⟨360756902177094504402271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481009202902792672536361 360756902177094504402271)
                  ·
                    rfl

theorem cell20_790393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_790393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790393 prefixEnd_790393 := by exact prefixLift 790393
  have htrace : WordTrace (prefixWord ++ tailWord_790393) baseStart_790393 baseEnd_790393 := by
    simpa [prefixWord, tailWord_790393, baseEnd_790393] using wordTrace_append hprefix tailTrace_790393
  have hstable : (prefixWord ++ tailWord_790393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790393).length < 2 ^ (prefixWord ++ tailWord_790393).sum := by decide
  have hdescent : baseEnd_790393 < baseStart_790393 := by decide
  rcases family_descends (prefixWord ++ tailWord_790393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790404 : List Nat := [2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_790404 : Nat := 118140960795 + 790404 * 2 ^ 59
def prefixEnd_790404 : Nat := 4983230072969 + 3 ^ 40 * 790404 * 2
def baseEnd_790404 : Nat := 120253974292275785011853

theorem tailTrace_790404 : CollatzResearch.WordTrace tailWord_790404 prefixEnd_790404 120253974292275785011853 := by
  unfold tailWord_790404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14414201114254386550593133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19218934819005848734124177 14414201114254386550593133)
  ·
    refine ⟨5405325417845394956472425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14414201114254386550593133 5405325417845394956472425)
    ·
      refine ⟨4053994063384046217354319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5405325417845394956472425 4053994063384046217354319)
      ·
        refine ⟨6080991095076069326031479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053994063384046217354319 6080991095076069326031479)
        ·
          refine ⟨9121486642614103989047219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080991095076069326031479 9121486642614103989047219)
          ·
            refine ⟨13682229963921155983570829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121486642614103989047219 13682229963921155983570829)
            ·
              refine ⟨5130836236470433493839061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13682229963921155983570829 5130836236470433493839061)
              ·
                refine ⟨120253974292275785011853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5130836236470433493839061 120253974292275785011853)
                ·
                  rfl

theorem cell20_790404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_790404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790404 prefixEnd_790404 := by exact prefixLift 790404
  have htrace : WordTrace (prefixWord ++ tailWord_790404) baseStart_790404 baseEnd_790404 := by
    simpa [prefixWord, tailWord_790404, baseEnd_790404] using wordTrace_append hprefix tailTrace_790404
  have hstable : (prefixWord ++ tailWord_790404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790404).length < 2 ^ (prefixWord ++ tailWord_790404).sum := by decide
  have hdescent : baseEnd_790404 < baseStart_790404 := by decide
  rcases family_descends (prefixWord ++ tailWord_790404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790407 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_790407 : Nat := 118140960795 + 790407 * 2 ^ 59
def prefixEnd_790407 : Nat := 4983230072969 + 3 ^ 40 * 790407 * 2
def baseEnd_790407 : Nat := 360763292158572677935547

theorem tailTrace_790407 : CollatzResearch.WordTrace tailWord_790407 prefixEnd_790407 360763292158572677935547 := by
  unfold tailWord_790407
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828511647497904613545475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19219007764998603075696983 28828511647497904613545475)
  ·
    refine ⟨43242767471246856920318213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28828511647497904613545475 43242767471246856920318213)
    ·
      refine ⟨8108018900858785672559665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43242767471246856920318213 8108018900858785672559665)
      ·
        refine ⟨6081014175644089254419749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8108018900858785672559665 6081014175644089254419749)
        ·
          refine ⟨1140190157933266735203703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6081014175644089254419749 1140190157933266735203703)
          ·
            refine ⟨1710285236899900102805555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140190157933266735203703 1710285236899900102805555)
            ·
              refine ⟨2565427855349850154208333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710285236899900102805555 2565427855349850154208333)
              ·
                refine ⟨962035445756193807828125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2565427855349850154208333 962035445756193807828125)
                ·
                  refine ⟨360763292158572677935547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962035445756193807828125 360763292158572677935547)
                  ·
                    rfl

theorem cell20_790407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_790407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790407 prefixEnd_790407 := by exact prefixLift 790407
  have htrace : WordTrace (prefixWord ++ tailWord_790407) baseStart_790407 baseEnd_790407 := by
    simpa [prefixWord, tailWord_790407, baseEnd_790407] using wordTrace_append hprefix tailTrace_790407
  have hstable : (prefixWord ++ tailWord_790407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790407).length < 2 ^ (prefixWord ++ tailWord_790407).sum := by decide
  have hdescent : baseEnd_790407 < baseStart_790407 := by decide
  rcases family_descends (prefixWord ++ tailWord_790407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790487 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_790487 : Nat := 118140960795 + 790487 * 2 ^ 59
def prefixEnd_790487 : Nat := 4983230072969 + 3 ^ 40 * 790487 * 2
def baseEnd_790487 : Nat := 360799806338447955268553

theorem tailTrace_790487 : CollatzResearch.WordTrace tailWord_790487 prefixEnd_790487 360799806338447955268553 := by
  unfold tailWord_790487
  simp only [CollatzResearch.WordTrace]
  refine ⟨28831429487208078276457715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19220952991472052184305143 28831429487208078276457715)
  ·
    refine ⟨43247144230812117414686573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28831429487208078276457715 43247144230812117414686573)
    ·
      refine ⟨16217679086554544030507465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43247144230812117414686573 16217679086554544030507465)
      ·
        refine ⟨12163259314915908022880599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16217679086554544030507465 12163259314915908022880599)
        ·
          refine ⟨18244888972373862034320899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12163259314915908022880599 18244888972373862034320899)
          ·
            refine ⟨27367333458560793051481349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18244888972373862034320899 27367333458560793051481349)
            ·
              refine ⟨5131375023480148697152753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27367333458560793051481349 5131375023480148697152753)
              ·
                refine ⟨3848531267610111522864565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5131375023480148697152753 3848531267610111522864565)
                ·
                  refine ⟨360799806338447955268553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3848531267610111522864565 360799806338447955268553)
                  ·
                    rfl

theorem cell20_790487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_790487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790487 prefixEnd_790487 := by exact prefixLift 790487
  have htrace : WordTrace (prefixWord ++ tailWord_790487) baseStart_790487 baseEnd_790487 := by
    simpa [prefixWord, tailWord_790487, baseEnd_790487] using wordTrace_append hprefix tailTrace_790487
  have hstable : (prefixWord ++ tailWord_790487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790487).length < 2 ^ (prefixWord ++ tailWord_790487).sum := by decide
  have hdescent : baseEnd_790487 < baseStart_790487 := by decide
  rcases family_descends (prefixWord ++ tailWord_790487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790511 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_790511 : Nat := 118140960795 + 790511 * 2 ^ 59
def prefixEnd_790511 : Nat := 4983230072969 + 3 ^ 40 * 790511 * 2
def baseEnd_790511 : Nat := 360810760592410538468455

theorem tailTrace_790511 : CollatzResearch.WordTrace tailWord_790511 prefixEnd_790511 360810760592410538468455 := by
  unfold tailWord_790511
  simp only [CollatzResearch.WordTrace]
  refine ⟨28832304839121130375331387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19221536559414086916887591 28832304839121130375331387)
  ·
    refine ⟨43248457258681695562997081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28832304839121130375331387 43248457258681695562997081)
    ·
      refine ⟨32436342944011271672247811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43248457258681695562997081 32436342944011271672247811)
      ·
        refine ⟨48654514416016907508371717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32436342944011271672247811 48654514416016907508371717)
        ·
          refine ⟨9122721453003170157819697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48654514416016907508371717 9122721453003170157819697)
          ·
            refine ⟨6842041089752377618364773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9122721453003170157819697 6842041089752377618364773)
            ·
              refine ⟨1282882704328570803443395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6842041089752377618364773 1282882704328570803443395)
              ·
                refine ⟨1924324056492856205165093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282882704328570803443395 1924324056492856205165093)
                ·
                  refine ⟨360810760592410538468455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924324056492856205165093 360810760592410538468455)
                  ·
                    rfl

theorem cell20_790511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_790511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790511 prefixEnd_790511 := by exact prefixLift 790511
  have htrace : WordTrace (prefixWord ++ tailWord_790511) baseStart_790511 baseEnd_790511 := by
    simpa [prefixWord, tailWord_790511, baseEnd_790511] using wordTrace_append hprefix tailTrace_790511
  have hstable : (prefixWord ++ tailWord_790511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790511).length < 2 ^ (prefixWord ++ tailWord_790511).sum := by decide
  have hdescent : baseEnd_790511 < baseStart_790511 := by decide
  rcases family_descends (prefixWord ++ tailWord_790511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790521 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 3]
def baseStart_790521 : Nat := 118140960795 + 790521 * 2 ^ 59
def prefixEnd_790521 : Nat := 4983230072969 + 3 ^ 40 * 790521 * 2
def baseEnd_790521 : Nat := 360815324864894948135081

theorem tailTrace_790521 : CollatzResearch.WordTrace tailWord_790521 prefixEnd_790521 360815324864894948135081 := by
  unfold tailWord_790521
  simp only [CollatzResearch.WordTrace]
  refine ⟨28832669569084902083195417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19221779712723268055463611 28832669569084902083195417)
  ·
    refine ⟨21624502176813676562396563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28832669569084902083195417 21624502176813676562396563)
    ·
      refine ⟨32436753265220514843594845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21624502176813676562396563 32436753265220514843594845)
      ·
        refine ⟨12163782474457693066348067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32436753265220514843594845 12163782474457693066348067)
        ·
          refine ⟨18245673711686539599522101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12163782474457693066348067 18245673711686539599522101)
          ·
            refine ⟨1710531910470613087455197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18245673711686539599522101 1710531910470613087455197)
            ·
              refine ⟨641449466426479907795699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1710531910470613087455197 641449466426479907795699)
              ·
                refine ⟨962174199639719861693549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641449466426479907795699 962174199639719861693549)
                ·
                  refine ⟨360815324864894948135081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962174199639719861693549 360815324864894948135081)
                  ·
                    rfl

theorem cell20_790521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_790521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790521 prefixEnd_790521 := by exact prefixLift 790521
  have htrace : WordTrace (prefixWord ++ tailWord_790521) baseStart_790521 baseEnd_790521 := by
    simpa [prefixWord, tailWord_790521, baseEnd_790521] using wordTrace_append hprefix tailTrace_790521
  have hstable : (prefixWord ++ tailWord_790521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790521).length < 2 ^ (prefixWord ++ tailWord_790521).sum := by decide
  have hdescent : baseEnd_790521 < baseStart_790521 := by decide
  rcases family_descends (prefixWord ++ tailWord_790521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790535 : List Nat := [1, 1, 4, 3, 1, 2, 4, 4]
def baseStart_790535 : Nat := 118140960795 + 790535 * 2 ^ 59
def prefixEnd_790535 : Nat := 4983230072969 + 3 ^ 40 * 790535 * 2
def baseEnd_790535 : Nat := 120273904948791040556119

theorem tailTrace_790535 : CollatzResearch.WordTrace tailWord_790535 prefixEnd_790535 120273904948791040556119 := by
  unfold tailWord_790535
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833180191034182474205059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19222120127356121649470039 28833180191034182474205059)
  ·
    refine ⟨43249770286551273711307589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28833180191034182474205059 43249770286551273711307589)
    ·
      refine ⟨8109331928728363820870173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43249770286551273711307589 8109331928728363820870173)
      ·
        refine ⟨3040999473273136432826315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8109331928728363820870173 3040999473273136432826315)
        ·
          refine ⟨4561499209909704649239473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040999473273136432826315 4561499209909704649239473)
          ·
            refine ⟨3421124407432278486929605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4561499209909704649239473 3421124407432278486929605)
            ·
              refine ⟨641460826393552216299301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3421124407432278486929605 641460826393552216299301)
              ·
                refine ⟨120273904948791040556119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 641460826393552216299301 120273904948791040556119)
                ·
                  rfl

theorem cell20_790535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_790535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790535 prefixEnd_790535 := by exact prefixLift 790535
  have htrace : WordTrace (prefixWord ++ tailWord_790535) baseStart_790535 baseEnd_790535 := by
    simpa [prefixWord, tailWord_790535, baseEnd_790535] using wordTrace_append hprefix tailTrace_790535
  have hstable : (prefixWord ++ tailWord_790535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790535).length < 2 ^ (prefixWord ++ tailWord_790535).sum := by decide
  have hdescent : baseEnd_790535 < baseStart_790535 := by decide
  rcases family_descends (prefixWord ++ tailWord_790535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790556 : List Nat := [2, 2, 3, 1, 3, 1, 8]
def baseStart_790556 : Nat := 118140960795 + 790556 * 2 ^ 59
def prefixEnd_790556 : Nat := 4983230072969 + 3 ^ 40 * 790556 * 2
def baseEnd_790556 : Nat := 40092366646510042440919

theorem tailTrace_790556 : CollatzResearch.WordTrace tailWord_790556 prefixEnd_790556 40092366646510042440919 := by
  unfold tailWord_790556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416973061979051530359761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19222630749305402040479681 14416973061979051530359761)
  ·
    refine ⟨10812729796484288647769821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14416973061979051530359761 10812729796484288647769821)
    ·
      refine ⟨4054773673681608242913683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10812729796484288647769821 4054773673681608242913683)
      ·
        refine ⟨6082160510522412364370525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054773673681608242913683 6082160510522412364370525)
        ·
          refine ⟨2280810191445904636638947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6082160510522412364370525 2280810191445904636638947)
          ·
            refine ⟨3421215287168856954958421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280810191445904636638947 3421215287168856954958421)
            ·
              refine ⟨40092366646510042440919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3421215287168856954958421 40092366646510042440919)
              ·
                rfl

theorem cell20_790556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_790556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790556 prefixEnd_790556 := by exact prefixLift 790556
  have htrace : WordTrace (prefixWord ++ tailWord_790556) baseStart_790556 baseEnd_790556 := by
    simpa [prefixWord, tailWord_790556, baseEnd_790556] using wordTrace_append hprefix tailTrace_790556
  have hstable : (prefixWord ++ tailWord_790556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790556).length < 2 ^ (prefixWord ++ tailWord_790556).sum := by decide
  have hdescent : baseEnd_790556 < baseStart_790556 := by decide
  rcases family_descends (prefixWord ++ tailWord_790556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790563 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_790563 : Nat := 118140960795 + 790563 * 2 ^ 59
def prefixEnd_790563 : Nat := 4983230072969 + 3 ^ 40 * 790563 * 2
def baseEnd_790563 : Nat := 360834494809329468734909

theorem tailTrace_790563 : CollatzResearch.WordTrace tailWord_790563 prefixEnd_790563 360834494809329468734909 := by
  unfold tailWord_790563
  simp only [CollatzResearch.WordTrace]
  refine ⟨28834201434932743256224343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19222800956621828837482895 28834201434932743256224343)
  ·
    refine ⟨43251302152399114884336515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28834201434932743256224343 43251302152399114884336515)
    ·
      refine ⟨64876953228598672326504773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43251302152399114884336515 64876953228598672326504773)
      ·
        refine ⟨12164428730362251061219645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64876953228598672326504773 12164428730362251061219645)
        ·
          refine ⟨4561660773885844147957367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12164428730362251061219645 4561660773885844147957367)
          ·
            refine ⟨6842491160828766221936051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561660773885844147957367 6842491160828766221936051)
            ·
              refine ⟨10263736741243149332904077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842491160828766221936051 10263736741243149332904077)
              ·
                refine ⟨3848901277966180999839029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10263736741243149332904077 3848901277966180999839029)
                ·
                  refine ⟨360834494809329468734909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3848901277966180999839029 360834494809329468734909)
                  ·
                    rfl

theorem cell20_790563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_790563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790563 prefixEnd_790563 := by exact prefixLift 790563
  have htrace : WordTrace (prefixWord ++ tailWord_790563) baseStart_790563 baseEnd_790563 := by
    simpa [prefixWord, tailWord_790563, baseEnd_790563] using wordTrace_append hprefix tailTrace_790563
  have hstable : (prefixWord ++ tailWord_790563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790563).length < 2 ^ (prefixWord ++ tailWord_790563).sum := by decide
  have hdescent : baseEnd_790563 < baseStart_790563 := by decide
  rcases family_descends (prefixWord ++ tailWord_790563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790614 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_790614 : Nat := 118140960795 + 790614 * 2 ^ 59
def prefixEnd_790614 : Nat := 4983230072969 + 3 ^ 40 * 790614 * 2
def baseEnd_790614 : Nat := 360857772598999958034701

theorem tailTrace_790614 : CollatzResearch.WordTrace tailWord_790614 prefixEnd_790614 360857772598999958034701 := by
  unfold tailWord_790614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802253847359248685395681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19224041038498652644220597 1802253847359248685395681)
  ·
    refine ⟨1351690385519436514046761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802253847359248685395681 1351690385519436514046761)
    ·
      refine ⟨1013767789139577385535071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1351690385519436514046761 1013767789139577385535071)
      ·
        refine ⟨1520651683709366078302607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013767789139577385535071 1520651683709366078302607)
        ·
          refine ⟨2280977525564049117453911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520651683709366078302607 2280977525564049117453911)
          ·
            refine ⟨3421466288346073676180867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280977525564049117453911 3421466288346073676180867)
            ·
              refine ⟨5132199432519110514271301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421466288346073676180867 5132199432519110514271301)
              ·
                refine ⟨962287393597333221425869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5132199432519110514271301 962287393597333221425869)
                ·
                  refine ⟨360857772598999958034701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962287393597333221425869 360857772598999958034701)
                  ·
                    rfl

theorem cell20_790614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_790614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790614 prefixEnd_790614 := by exact prefixLift 790614
  have htrace : WordTrace (prefixWord ++ tailWord_790614) baseStart_790614 baseEnd_790614 := by
    simpa [prefixWord, tailWord_790614, baseEnd_790614] using wordTrace_append hprefix tailTrace_790614
  have hstable : (prefixWord ++ tailWord_790614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790614).length < 2 ^ (prefixWord ++ tailWord_790614).sum := by decide
  have hdescent : baseEnd_790614 < baseStart_790614 := by decide
  rcases family_descends (prefixWord ++ tailWord_790614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790618 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_790618 : Nat := 118140960795 + 790618 * 2 ^ 59
def prefixEnd_790618 : Nat := 4983230072969 + 3 ^ 40 * 790618 * 2
def baseEnd_790618 : Nat := 360859598307993721901351

theorem tailTrace_790618 : CollatzResearch.WordTrace tailWord_790618 prefixEnd_790618 360859598307993721901351 := by
  unfold tailWord_790618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209051862433371912369127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19224138299822325099651005 7209051862433371912369127)
  ·
    refine ⟨10813577793650057868553691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7209051862433371912369127 10813577793650057868553691)
    ·
      refine ⟨16220366690475086802830537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10813577793650057868553691 16220366690475086802830537)
      ·
        refine ⟨12165275017856315102122903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16220366690475086802830537 12165275017856315102122903)
        ·
          refine ⟨18247912526784472653184355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12165275017856315102122903 18247912526784472653184355)
          ·
            refine ⟨27371868790176708979776533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18247912526784472653184355 27371868790176708979776533)
            ·
              refine ⟨1283056349539533233427025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27371868790176708979776533 1283056349539533233427025)
              ·
                refine ⟨962292262154649925070269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283056349539533233427025 962292262154649925070269)
                ·
                  refine ⟨360859598307993721901351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962292262154649925070269 360859598307993721901351)
                  ·
                    rfl

theorem cell20_790618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_790618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790618 prefixEnd_790618 := by exact prefixLift 790618
  have htrace : WordTrace (prefixWord ++ tailWord_790618) baseStart_790618 baseEnd_790618 := by
    simpa [prefixWord, tailWord_790618, baseEnd_790618] using wordTrace_append hprefix tailTrace_790618
  have hstable : (prefixWord ++ tailWord_790618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790618).length < 2 ^ (prefixWord ++ tailWord_790618).sum := by decide
  have hdescent : baseEnd_790618 < baseStart_790618 := by decide
  rcases family_descends (prefixWord ++ tailWord_790618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790649 : List Nat := [1, 2, 1, 3, 4, 2, 3, 4]
def baseStart_790649 : Nat := 118140960795 + 790649 * 2 ^ 59
def prefixEnd_790649 : Nat := 4983230072969 + 3 ^ 40 * 790649 * 2
def baseEnd_790649 : Nat := 120291249184231797289297

theorem tailTrace_790649 : CollatzResearch.WordTrace tailWord_790649 prefixEnd_790649 120291249184231797289297 := by
  unfold tailWord_790649
  simp only [CollatzResearch.WordTrace]
  refine ⟨28837338112621179943855001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19224892075080786629236667 28837338112621179943855001)
  ·
    refine ⟨21628003584465884957891251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28837338112621179943855001 21628003584465884957891251)
    ·
      refine ⟨32442005376698827436836877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21628003584465884957891251 32442005376698827436836877)
      ·
        refine ⟨12165752016262060288813829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32442005376698827436836877 12165752016262060288813829)
        ·
          refine ⟨2281078503049136304152593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12165752016262060288813829 2281078503049136304152593)
          ·
            refine ⟨1710808877286852228114445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281078503049136304152593 1710808877286852228114445)
            ·
              refine ⟨641553328982569585542917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1710808877286852228114445 641553328982569585542917)
              ·
                refine ⟨120291249184231797289297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 641553328982569585542917 120291249184231797289297)
                ·
                  rfl

theorem cell20_790649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_790649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790649 prefixEnd_790649 := by exact prefixLift 790649
  have htrace : WordTrace (prefixWord ++ tailWord_790649) baseStart_790649 baseEnd_790649 := by
    simpa [prefixWord, tailWord_790649, baseEnd_790649] using wordTrace_append hprefix tailTrace_790649
  have hstable : (prefixWord ++ tailWord_790649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790649).length < 2 ^ (prefixWord ++ tailWord_790649).sum := by decide
  have hdescent : baseEnd_790649 < baseStart_790649 := by decide
  rcases family_descends (prefixWord ++ tailWord_790649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790677 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_790677 : Nat := 118140960795 + 790677 * 2 ^ 59
def prefixEnd_790677 : Nat := 4983230072969 + 3 ^ 40 * 790677 * 2
def baseEnd_790677 : Nat := 360886527515651738934443

theorem tailTrace_790677 : CollatzResearch.WordTrace tailWord_790677 prefixEnd_790677 360886527515651738934443 := by
  unfold tailWord_790677
  simp only [CollatzResearch.WordTrace]
  refine ⟨28838359356519740725874285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19225572904346493817249523 28838359356519740725874285)
  ·
    refine ⟨10814384758694902772202857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28838359356519740725874285 10814384758694902772202857)
    ·
      refine ⟨8110788569021177079152143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10814384758694902772202857 8110788569021177079152143)
      ·
        refine ⟨12166182853531765618728215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8110788569021177079152143 12166182853531765618728215)
        ·
          refine ⟨18249274280297648428092323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12166182853531765618728215 18249274280297648428092323)
          ·
            refine ⟨27373911420446472642138485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18249274280297648428092323 27373911420446472642138485)
            ·
              refine ⟨2566304195666856810200483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27373911420446472642138485 2566304195666856810200483)
              ·
                refine ⟨3849456293500285215300725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566304195666856810200483 3849456293500285215300725)
                ·
                  refine ⟨360886527515651738934443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849456293500285215300725 360886527515651738934443)
                  ·
                    rfl

theorem cell20_790677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_790677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790677 prefixEnd_790677 := by exact prefixLift 790677
  have htrace : WordTrace (prefixWord ++ tailWord_790677) baseStart_790677 baseEnd_790677 := by
    simpa [prefixWord, tailWord_790677, baseEnd_790677] using wordTrace_append hprefix tailTrace_790677
  have hstable : (prefixWord ++ tailWord_790677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790677).length < 2 ^ (prefixWord ++ tailWord_790677).sum := by decide
  have hdescent : baseEnd_790677 < baseStart_790677 := by decide
  rcases family_descends (prefixWord ++ tailWord_790677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790680 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_790680 : Nat := 118140960795 + 790680 * 2 ^ 59
def prefixEnd_790680 : Nat := 4983230072969 + 3 ^ 40 * 790680 * 2
def baseEnd_790680 : Nat := 360887896797397061834431

theorem tailTrace_790680 : CollatzResearch.WordTrace tailWord_790680 prefixEnd_790680 360887896797397061834431 := by
  unfold tailWord_790680
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419234387754436119116747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19225645850339248158822329 14419234387754436119116747)
  ·
    refine ⟨21628851581631654178675121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14419234387754436119116747 21628851581631654178675121)
    ·
      refine ⟨16221638686223740634006341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21628851581631654178675121 16221638686223740634006341)
      ·
        refine ⟨3041557253666951368876189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16221638686223740634006341 3041557253666951368876189)
        ·
          refine ⟨1140583970125106763328571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3041557253666951368876189 1140583970125106763328571)
          ·
            refine ⟨1710875955187660144992857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140583970125106763328571 1710875955187660144992857)
            ·
              refine ⟨1283156966390745108744643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710875955187660144992857 1283156966390745108744643)
              ·
                refine ⟨1924735449586117663116965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283156966390745108744643 1924735449586117663116965)
                ·
                  refine ⟨360887896797397061834431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924735449586117663116965 360887896797397061834431)
                  ·
                    rfl

theorem cell20_790680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_790680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790680 prefixEnd_790680 := by exact prefixLift 790680
  have htrace : WordTrace (prefixWord ++ tailWord_790680) baseStart_790680 baseEnd_790680 := by
    simpa [prefixWord, tailWord_790680, baseEnd_790680] using wordTrace_append hprefix tailTrace_790680
  have hstable : (prefixWord ++ tailWord_790680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790680).length < 2 ^ (prefixWord ++ tailWord_790680).sum := by decide
  have hdescent : baseEnd_790680 < baseStart_790680 := by decide
  rcases family_descends (prefixWord ++ tailWord_790680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790690 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_790690 : Nat := 118140960795 + 790690 * 2 ^ 59
def prefixEnd_790690 : Nat := 4983230072969 + 3 ^ 40 * 790690 * 2
def baseEnd_790690 : Nat := 360892461069881471501057

theorem tailTrace_790690 : CollatzResearch.WordTrace tailWord_790690 prefixEnd_790690 360892461069881471501057 := by
  unfold tailWord_790690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209708376368160986524381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19225889003648429297398349 7209708376368160986524381)
  ·
    refine ⟨2703640641138060369946643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7209708376368160986524381 2703640641138060369946643)
    ·
      refine ⟨4055460961707090554919965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703640641138060369946643 4055460961707090554919965)
      ·
        refine ⟨1520797860640158958094987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4055460961707090554919965 1520797860640158958094987)
        ·
          refine ⟨2281196790960238437142481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520797860640158958094987 2281196790960238437142481)
          ·
            refine ⟨1710897593220178827856861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281196790960238437142481 1710897593220178827856861)
            ·
              refine ⟨641586597457567060446323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1710897593220178827856861 641586597457567060446323)
              ·
                refine ⟨962379896186350590669485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641586597457567060446323 962379896186350590669485)
                ·
                  refine ⟨360892461069881471501057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962379896186350590669485 360892461069881471501057)
                  ·
                    rfl

theorem cell20_790690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_790690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790690 prefixEnd_790690 := by exact prefixLift 790690
  have htrace : WordTrace (prefixWord ++ tailWord_790690) baseStart_790690 baseEnd_790690 := by
    simpa [prefixWord, tailWord_790690, baseEnd_790690] using wordTrace_append hprefix tailTrace_790690
  have hstable : (prefixWord ++ tailWord_790690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790690).length < 2 ^ (prefixWord ++ tailWord_790690).sum := by decide
  have hdescent : baseEnd_790690 < baseStart_790690 := by decide
  rcases family_descends (prefixWord ++ tailWord_790690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790742 : List Nat := [5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_790742 : Nat := 118140960795 + 790742 * 2 ^ 59
def prefixEnd_790742 : Nat := 4983230072969 + 3 ^ 40 * 790742 * 2
def baseEnd_790742 : Nat := 120305398428933467255837

theorem tailTrace_790742 : CollatzResearch.WordTrace tailWord_790742 prefixEnd_790742 120305398428933467255837 := by
  unfold tailWord_790742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802545631330266051686905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19227153400856171217993653 1802545631330266051686905)
  ·
    refine ⟨1351909223497699538765179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802545631330266051686905 1351909223497699538765179)
    ·
      refine ⟨2027863835246549308147769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351909223497699538765179 2027863835246549308147769)
      ·
        refine ⟨1520897876434911981110827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027863835246549308147769 1520897876434911981110827)
        ·
          refine ⟨2281346814652367971666241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520897876434911981110827 2281346814652367971666241)
          ·
            refine ⟨1711010110989275978749681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281346814652367971666241 1711010110989275978749681)
            ·
              refine ⟨1283257583241956984062261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711010110989275978749681 1283257583241956984062261)
              ·
                refine ⟨120305398428933467255837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1283257583241956984062261 120305398428933467255837)
                ·
                  rfl

theorem cell20_790742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_790742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790742 prefixEnd_790742 := by exact prefixLift 790742
  have htrace : WordTrace (prefixWord ++ tailWord_790742) baseStart_790742 baseEnd_790742 := by
    simpa [prefixWord, tailWord_790742, baseEnd_790742] using wordTrace_append hprefix tailTrace_790742
  have hstable : (prefixWord ++ tailWord_790742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790742).length < 2 ^ (prefixWord ++ tailWord_790742).sum := by decide
  have hdescent : baseEnd_790742 < baseStart_790742 := by decide
  rcases family_descends (prefixWord ++ tailWord_790742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790749 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_790749 : Nat := 118140960795 + 790749 * 2 ^ 59
def prefixEnd_790749 : Nat := 4983230072969 + 3 ^ 40 * 790749 * 2
def baseEnd_790749 : Nat := 360919390277539488534149

theorem tailTrace_790749 : CollatzResearch.WordTrace tailWord_790749 prefixEnd_790749 360919390277539488534149 := by
  unfold tailWord_790749
  simp only [CollatzResearch.WordTrace]
  refine ⟨28840985412258897022495301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19227323608172598014996867 28840985412258897022495301)
  ·
    refine ⟨5407684764798543191717869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28840985412258897022495301 5407684764798543191717869)
    ·
      refine ⟨2027881786799453696894201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5407684764798543191717869 2027881786799453696894201)
      ·
        refine ⟨1520911340099590272670651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027881786799453696894201 1520911340099590272670651)
        ·
          refine ⟨2281367010149385409005977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520911340099590272670651 2281367010149385409005977)
          ·
            refine ⟨1711025257612039056754483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281367010149385409005977 1711025257612039056754483)
            ·
              refine ⟨2566537886418058585131725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711025257612039056754483 2566537886418058585131725)
              ·
                refine ⟨962451707406771969424397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2566537886418058585131725 962451707406771969424397)
                ·
                  refine ⟨360919390277539488534149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962451707406771969424397 360919390277539488534149)
                  ·
                    rfl

theorem cell20_790749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_790749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790749 prefixEnd_790749 := by exact prefixLift 790749
  have htrace : WordTrace (prefixWord ++ tailWord_790749) baseStart_790749 baseEnd_790749 := by
    simpa [prefixWord, tailWord_790749, baseEnd_790749] using wordTrace_append hprefix tailTrace_790749
  have hstable : (prefixWord ++ tailWord_790749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790749).length < 2 ^ (prefixWord ++ tailWord_790749).sum := by decide
  have hdescent : baseEnd_790749 < baseStart_790749 := by decide
  rcases family_descends (prefixWord ++ tailWord_790749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790815 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_790815 : Nat := 118140960795 + 790815 * 2 ^ 59
def prefixEnd_790815 : Nat := 4983230072969 + 3 ^ 40 * 790815 * 2
def baseEnd_790815 : Nat := 360949514475936592333879

theorem tailTrace_790815 : CollatzResearch.WordTrace tailWord_790815 prefixEnd_790815 360949514475936592333879 := by
  unfold tailWord_790815
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843392630019790294397899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19228928420013193529598599 28843392630019790294397899)
  ·
    refine ⟨43265088945029685441596849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28843392630019790294397899 43265088945029685441596849)
    ·
      refine ⟨32448816708772264081197637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43265088945029685441596849 32448816708772264081197637)
      ·
        refine ⟨6084153132894799515224557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32448816708772264081197637 6084153132894799515224557)
        ·
          refine ⟨2281557424835549818209209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6084153132894799515224557 2281557424835549818209209)
          ·
            refine ⟨1711168068626662363656907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281557424835549818209209 1711168068626662363656907)
            ·
              refine ⟨2566752102939993545485361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711168068626662363656907 2566752102939993545485361)
              ·
                refine ⟨1925064077204995159114021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566752102939993545485361 1925064077204995159114021)
                ·
                  refine ⟨360949514475936592333879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925064077204995159114021 360949514475936592333879)
                  ·
                    rfl

theorem cell20_790815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_790815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790815 prefixEnd_790815 := by exact prefixLift 790815
  have htrace : WordTrace (prefixWord ++ tailWord_790815) baseStart_790815 baseEnd_790815 := by
    simpa [prefixWord, tailWord_790815, baseEnd_790815] using wordTrace_append hprefix tailTrace_790815
  have hstable : (prefixWord ++ tailWord_790815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790815).length < 2 ^ (prefixWord ++ tailWord_790815).sum := by decide
  have hdescent : baseEnd_790815 < baseStart_790815 := by decide
  rcases family_descends (prefixWord ++ tailWord_790815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
