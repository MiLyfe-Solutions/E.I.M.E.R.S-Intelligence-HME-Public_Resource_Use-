import V185TrunkScan22Chunk290

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2594692 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2594692 : Nat := 118140960795 + 2594692 * 2 ^ 59
def prefixEnd_2594692 : Nat := 4983230072969 + 3 ^ 40 * 2594692 * 2
def baseEnd_2594692 : Nat := 888216097583911659544823

theorem tailTrace_2594692 : CollatzResearch.WordTrace tailWord_2594692 prefixEnd_2594692 888216097583911659544823 := by
  unfold tailWord_2594692
  simp only [CollatzResearch.WordTrace]
  refine ⟨47318095957940748479341165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63090794610587664639121553 47318095957940748479341165)
  ·
    refine ⟨17744285984227780679752937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47318095957940748479341165 17744285984227780679752937)
    ·
      refine ⟨13308214488170835509814703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17744285984227780679752937 13308214488170835509814703)
      ·
        refine ⟨19962321732256253264722055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13308214488170835509814703 19962321732256253264722055)
        ·
          refine ⟨29943482598384379897083083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19962321732256253264722055 29943482598384379897083083)
          ·
            refine ⟨44915223897576569845624625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29943482598384379897083083 44915223897576569845624625)
            ·
              refine ⟨33686417923182427384218469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44915223897576569845624625 33686417923182427384218469)
              ·
                refine ⟨6316203360596705134540963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33686417923182427384218469 6316203360596705134540963)
                ·
                  refine ⟨9474305040895057701811445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316203360596705134540963 9474305040895057701811445)
                  ·
                    refine ⟨888216097583911659544823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9474305040895057701811445 888216097583911659544823)
                    ·
                      rfl

theorem cell22_2594692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2594692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594692 prefixEnd_2594692 := by exact prefixLift 2594692
  have htrace : WordTrace (prefixWord ++ tailWord_2594692) baseStart_2594692 baseEnd_2594692 := by
    simpa [prefixWord, tailWord_2594692, baseEnd_2594692] using wordTrace_append hprefix tailTrace_2594692
  have hstable : (prefixWord ++ tailWord_2594692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594692).length < 2 ^ (prefixWord ++ tailWord_2594692).sum := by decide
  have hdescent : baseEnd_2594692 < baseStart_2594692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594705 : List Nat := [1, 2, 2, 1, 1, 1, 14]
def baseStart_2594705 : Nat := 118140960795 + 2594705 * 2 ^ 59
def prefixEnd_2594705 : Nat := 4983230072969 + 3 ^ 40 * 2594705 * 2
def baseEnd_2594705 : Nat := 32897057324058665147029

theorem tailTrace_2594705 : CollatzResearch.WordTrace tailWord_2594705 prefixEnd_2594705 32897057324058665147029 := by
  unfold tailWord_2594705
  simp only [CollatzResearch.WordTrace]
  refine ⟨94636666064834400178905569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63091110709889600119270379 94636666064834400178905569)
  ·
    refine ⟨70977499548625800134179177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94636666064834400178905569 70977499548625800134179177)
    ·
      refine ⟨53233124661469350100634383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70977499548625800134179177 53233124661469350100634383)
      ·
        refine ⟨79849686992204025150951575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53233124661469350100634383 79849686992204025150951575)
        ·
          refine ⟨119774530488306037726427363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79849686992204025150951575 119774530488306037726427363)
          ·
            refine ⟨179661795732459056589641045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119774530488306037726427363 179661795732459056589641045)
            ·
              refine ⟨32897057324058665147029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 179661795732459056589641045 32897057324058665147029)
              ·
                rfl

theorem cell22_2594705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 14].length) (baseStart_2594705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594705 prefixEnd_2594705 := by exact prefixLift 2594705
  have htrace : WordTrace (prefixWord ++ tailWord_2594705) baseStart_2594705 baseEnd_2594705 := by
    simpa [prefixWord, tailWord_2594705, baseEnd_2594705] using wordTrace_append hprefix tailTrace_2594705
  have hstable : (prefixWord ++ tailWord_2594705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594705).length < 2 ^ (prefixWord ++ tailWord_2594705).sum := by decide
  have hdescent : baseEnd_2594705 < baseStart_2594705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594709 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_2594709 : Nat := 118140960795 + 2594709 * 2 ^ 59
def prefixEnd_2594709 : Nat := 4983230072969 + 3 ^ 40 * 2594709 * 2
def baseEnd_2594709 : Nat := 888221917031329281869771

theorem tailTrace_2594709 : CollatzResearch.WordTrace tailWord_2594709 prefixEnd_2594709 888221917031329281869771 := by
  unfold tailWord_2594709
  simp only [CollatzResearch.WordTrace]
  refine ⟨94636811956819908862051181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63091207971213272574700787 94636811956819908862051181)
  ·
    refine ⟨35488804483807465823269193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94636811956819908862051181 35488804483807465823269193)
    ·
      refine ⟨26616603362855599367451895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35488804483807465823269193 26616603362855599367451895)
      ·
        refine ⟨39924905044283399051177843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26616603362855599367451895 39924905044283399051177843)
        ·
          refine ⟨59887357566425098576766765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39924905044283399051177843 59887357566425098576766765)
          ·
            refine ⟨22457759087409411966287537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59887357566425098576766765 22457759087409411966287537)
            ·
              refine ⟨16843319315557058974715653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22457759087409411966287537 16843319315557058974715653)
              ·
                refine ⟨3158122371666948557759185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16843319315557058974715653 3158122371666948557759185)
                ·
                  refine ⟨2368591778750211418319389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3158122371666948557759185 2368591778750211418319389)
                  ·
                    refine ⟨888221917031329281869771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368591778750211418319389 888221917031329281869771)
                    ·
                      rfl

theorem cell22_2594709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_2594709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594709 prefixEnd_2594709 := by exact prefixLift 2594709
  have htrace : WordTrace (prefixWord ++ tailWord_2594709) baseStart_2594709 baseEnd_2594709 := by
    simpa [prefixWord, tailWord_2594709, baseEnd_2594709] using wordTrace_append hprefix tailTrace_2594709
  have hstable : (prefixWord ++ tailWord_2594709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594709).length < 2 ^ (prefixWord ++ tailWord_2594709).sum := by decide
  have hdescent : baseEnd_2594709 < baseStart_2594709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594711 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 4]
def baseStart_2594711 : Nat := 118140960795 + 2594711 * 2 ^ 59
def prefixEnd_2594711 : Nat := 4983230072969 + 3 ^ 40 * 2594711 * 2
def baseEnd_2594711 : Nat := 296074200557400647773255

theorem tailTrace_2594711 : CollatzResearch.WordTrace tailWord_2594711 prefixEnd_2594711 296074200557400647773255 := by
  unfold tailWord_2594711
  simp only [CollatzResearch.WordTrace]
  refine ⟨94636884902812663203623987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63091256601875108802415991 94636884902812663203623987)
  ·
    refine ⟨141955327354218994805435981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94636884902812663203623987 141955327354218994805435981)
    ·
      refine ⟨53233247757832123052038493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141955327354218994805435981 53233247757832123052038493)
      ·
        refine ⟨19962467909187046144514435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53233247757832123052038493 19962467909187046144514435)
        ·
          refine ⟨29943701863780569216771653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19962467909187046144514435 29943701863780569216771653)
          ·
            refine ⟨5614444099458856728144685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29943701863780569216771653 5614444099458856728144685)
            ·
              refine ⟨2105416537297071273054257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5614444099458856728144685 2105416537297071273054257)
              ·
                refine ⟨1579062402972803454790693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105416537297071273054257 1579062402972803454790693)
                ·
                  refine ⟨296074200557400647773255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1579062402972803454790693 296074200557400647773255)
                  ·
                    rfl

theorem cell22_2594711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 4].length) (baseStart_2594711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594711 prefixEnd_2594711 := by exact prefixLift 2594711
  have htrace : WordTrace (prefixWord ++ tailWord_2594711) baseStart_2594711 baseEnd_2594711 := by
    simpa [prefixWord, tailWord_2594711, baseEnd_2594711] using wordTrace_append hprefix tailTrace_2594711
  have hstable : (prefixWord ++ tailWord_2594711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594711).length < 2 ^ (prefixWord ++ tailWord_2594711).sum := by decide
  have hdescent : baseEnd_2594711 < baseStart_2594711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594812 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_2594812 : Nat := 118140960795 + 2594812 * 2 ^ 59
def prefixEnd_2594812 : Nat := 4983230072969 + 3 ^ 40 * 2594812 * 2
def baseEnd_2594812 : Nat := 296085725345423782181485

theorem tailTrace_2594812 : CollatzResearch.WordTrace tailWord_2594812 prefixEnd_2594812 296085725345423782181485 := by
  unfold tailWord_2594812
  simp only [CollatzResearch.WordTrace]
  refine ⟨47320284337723378726525345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63093712450297838302033793 47320284337723378726525345)
  ·
    refine ⟨35490213253292534044894009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47320284337723378726525345 35490213253292534044894009)
    ·
      refine ⟨26617659939969400533670507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35490213253292534044894009 26617659939969400533670507)
      ·
        refine ⟨39926489909954100800505761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26617659939969400533670507 39926489909954100800505761)
        ·
          refine ⟨29944867432465575600379321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39926489909954100800505761 29944867432465575600379321)
          ·
            refine ⟨22458650574349181700284491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29944867432465575600379321 22458650574349181700284491)
            ·
              refine ⟨33687975861523772550426737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22458650574349181700284491 33687975861523772550426737)
              ·
                refine ⟨25265981896142829412820053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33687975861523772550426737 25265981896142829412820053)
                ·
                  refine ⟨296085725345423782181485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25265981896142829412820053 296085725345423782181485)
                  ·
                    rfl

theorem cell22_2594812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_2594812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594812 prefixEnd_2594812 := by exact prefixLift 2594812
  have htrace : WordTrace (prefixWord ++ tailWord_2594812) baseStart_2594812 baseEnd_2594812 := by
    simpa [prefixWord, tailWord_2594812, baseEnd_2594812] using wordTrace_append hprefix tailTrace_2594812
  have hstable : (prefixWord ++ tailWord_2594812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594812).length < 2 ^ (prefixWord ++ tailWord_2594812).sum := by decide
  have hdescent : baseEnd_2594812 < baseStart_2594812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2594940 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_2594940 : Nat := 118140960795 + 2594940 * 2 ^ 59
def prefixEnd_2594940 : Nat := 4983230072969 + 3 ^ 40 * 2594940 * 2
def baseEnd_2594940 : Nat := 888300993052121679344063

theorem tailTrace_2594940 : CollatzResearch.WordTrace tailWord_2594940 prefixEnd_2594940 888300993052121679344063 := by
  unfold tailWord_2594940
  simp only [CollatzResearch.WordTrace]
  refine ⟨47322618609491517656855137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63096824812655356875806849 47322618609491517656855137)
  ·
    refine ⟨35491963957118638242641353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47322618609491517656855137 35491963957118638242641353)
    ·
      refine ⟨26618972967838978681981015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35491963957118638242641353 26618972967838978681981015)
      ·
        refine ⟨39928459451758468022971523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26618972967838978681981015 39928459451758468022971523)
        ·
          refine ⟨59892689177637702034457285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39928459451758468022971523 59892689177637702034457285)
          ·
            refine ⟨11229879220807069131460741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59892689177637702034457285 11229879220807069131460741)
            ·
              refine ⟨2105602353901325462148889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11229879220807069131460741 2105602353901325462148889)
              ·
                refine ⟨1579201765425994096611667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105602353901325462148889 1579201765425994096611667)
                ·
                  refine ⟨2368802648138991144917501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579201765425994096611667 2368802648138991144917501)
                  ·
                    refine ⟨888300993052121679344063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368802648138991144917501 888300993052121679344063)
                    ·
                      rfl

theorem cell22_2594940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_2594940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2594940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2594940 prefixEnd_2594940 := by exact prefixLift 2594940
  have htrace : WordTrace (prefixWord ++ tailWord_2594940) baseStart_2594940 baseEnd_2594940 := by
    simpa [prefixWord, tailWord_2594940, baseEnd_2594940] using wordTrace_append hprefix tailTrace_2594940
  have hstable : (prefixWord ++ tailWord_2594940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2594940).length < 2 ^ (prefixWord ++ tailWord_2594940).sum := by decide
  have hdescent : baseEnd_2594940 < baseStart_2594940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2594940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595026 : List Nat := [3, 2, 2, 2, 1, 3, 1, 8]
def baseStart_2595026 : Nat := 118140960795 + 2595026 * 2 ^ 59
def prefixEnd_2595026 : Nat := 4983230072969 + 3 ^ 40 * 2595026 * 2
def baseEnd_2595026 : Nat := 98703381401071791299311

theorem tailTrace_2595026 : CollatzResearch.WordTrace tailWord_2595026 prefixEnd_2595026 98703381401071791299311 := by
  unfold tailWord_2595026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662093474167868000335233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63098915931114314667560621 23662093474167868000335233)
  ·
    refine ⟨17746570105625901000251425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23662093474167868000335233 17746570105625901000251425)
    ·
      refine ⟨13309927579219425750188569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17746570105625901000251425 13309927579219425750188569)
      ·
        refine ⟨9982445684414569312641427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13309927579219425750188569 9982445684414569312641427)
        ·
          refine ⟨14973668526621853968962141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982445684414569312641427 14973668526621853968962141)
          ·
            refine ⟨5615125697483195238360803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14973668526621853968962141 5615125697483195238360803)
            ·
              refine ⟨8422688546224792857541205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5615125697483195238360803 8422688546224792857541205)
              ·
                refine ⟨98703381401071791299311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8422688546224792857541205 98703381401071791299311)
                ·
                  rfl

theorem cell22_2595026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_2595026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595026 prefixEnd_2595026 := by exact prefixLift 2595026
  have htrace : WordTrace (prefixWord ++ tailWord_2595026) baseStart_2595026 baseEnd_2595026 := by
    simpa [prefixWord, tailWord_2595026, baseEnd_2595026] using wordTrace_append hprefix tailTrace_2595026
  have hstable : (prefixWord ++ tailWord_2595026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595026).length < 2 ^ (prefixWord ++ tailWord_2595026).sum := by decide
  have hdescent : baseEnd_2595026 < baseStart_2595026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595030 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2595030 : Nat := 118140960795 + 2595030 * 2 ^ 59
def prefixEnd_2595030 : Nat := 4983230072969 + 3 ^ 40 * 2595030 * 2
def baseEnd_2595030 : Nat := 888331801891391444593787

theorem tailTrace_2595030 : CollatzResearch.WordTrace tailWord_2595030 prefixEnd_2595030 888331801891391444593787 := by
  unfold tailWord_2595030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915532486791061292780409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63099013192437987122991029 5915532486791061292780409)
  ·
    refine ⟨4436649365093295969585307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5915532486791061292780409 4436649365093295969585307)
    ·
      refine ⟨6654974047639943954377961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4436649365093295969585307 6654974047639943954377961)
      ·
        refine ⟨4991230535729957965783471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6654974047639943954377961 4991230535729957965783471)
        ·
          refine ⟨7486845803594936948675207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991230535729957965783471 7486845803594936948675207)
          ·
            refine ⟨11230268705392405423012811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7486845803594936948675207 11230268705392405423012811)
            ·
              refine ⟨16845403058088608134519217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11230268705392405423012811 16845403058088608134519217)
              ·
                refine ⟨12634052293566456100889413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16845403058088608134519217 12634052293566456100889413)
                ·
                  refine ⟨2368884805043710518916765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12634052293566456100889413 2368884805043710518916765)
                  ·
                    refine ⟨888331801891391444593787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368884805043710518916765 888331801891391444593787)
                    ·
                      rfl

theorem cell22_2595030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2595030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595030 prefixEnd_2595030 := by exact prefixLift 2595030
  have htrace : WordTrace (prefixWord ++ tailWord_2595030) baseStart_2595030 baseEnd_2595030 := by
    simpa [prefixWord, tailWord_2595030, baseEnd_2595030] using wordTrace_append hprefix tailTrace_2595030
  have hstable : (prefixWord ++ tailWord_2595030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595030).length < 2 ^ (prefixWord ++ tailWord_2595030).sum := by decide
  have hdescent : baseEnd_2595030 < baseStart_2595030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595039 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_2595039 : Nat := 118140960795 + 2595039 * 2 ^ 59
def prefixEnd_2595039 : Nat := 4983230072969 + 3 ^ 40 * 2595039 * 2
def baseEnd_2595039 : Nat := 888334882775318421118759

theorem tailTrace_2595039 : CollatzResearch.WordTrace tailWord_2595039 prefixEnd_2595039 888334882775318421118759 := by
  unfold tailWord_2595039
  simp only [CollatzResearch.WordTrace]
  refine ⟨94648848045624375221564171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63099232030416250147709447 94648848045624375221564171)
  ·
    refine ⟨141973272068436562832346257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94648848045624375221564171 141973272068436562832346257)
    ·
      refine ⟨106479954051327422124259693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141973272068436562832346257 106479954051327422124259693)
      ·
        refine ⟨39929982769247783296597385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106479954051327422124259693 39929982769247783296597385)
        ·
          refine ⟨29947487076935837472448039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39929982769247783296597385 29947487076935837472448039)
          ·
            refine ⟨44921230615403756208672059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29947487076935837472448039 44921230615403756208672059)
            ·
              refine ⟨67381845923105634313008089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44921230615403756208672059 67381845923105634313008089)
              ·
                refine ⟨50536384442329225734756067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67381845923105634313008089 50536384442329225734756067)
                ·
                  refine ⟨75804576663493838602134101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50536384442329225734756067 75804576663493838602134101)
                  ·
                    refine ⟨888334882775318421118759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75804576663493838602134101 888334882775318421118759)
                    ·
                      rfl

theorem cell22_2595039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_2595039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595039 prefixEnd_2595039 := by exact prefixLift 2595039
  have htrace : WordTrace (prefixWord ++ tailWord_2595039) baseStart_2595039 baseEnd_2595039 := by
    simpa [prefixWord, tailWord_2595039, baseEnd_2595039] using wordTrace_append hprefix tailTrace_2595039
  have hstable : (prefixWord ++ tailWord_2595039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595039).length < 2 ^ (prefixWord ++ tailWord_2595039).sum := by decide
  have hdescent : baseEnd_2595039 < baseStart_2595039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595043 : List Nat := [1, 1, 1, 8, 1, 2, 8]
def baseStart_2595043 : Nat := 118140960795 + 2595043 * 2 ^ 59
def prefixEnd_2595043 : Nat := 4983230072969 + 3 ^ 40 * 2595043 * 2
def baseEnd_2595043 : Nat := 32901342668780138667361

theorem tailTrace_2595043 : CollatzResearch.WordTrace tailWord_2595043 prefixEnd_2595043 32901342668780138667361 := by
  unfold tailWord_2595043
  simp only [CollatzResearch.WordTrace]
  refine ⟨94648993937609883904709783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63099329291739922603139855 94648993937609883904709783)
  ·
    refine ⟨141973490906414825857064675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94648993937609883904709783 141973490906414825857064675)
    ·
      refine ⟨212960236359622238785597013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141973490906414825857064675 212960236359622238785597013)
      ·
        refine ⟨2495627769839323110768715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 212960236359622238785597013 2495627769839323110768715)
        ·
          refine ⟨3743441654758984666153073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495627769839323110768715 3743441654758984666153073)
          ·
            refine ⟨2807581241069238499614805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743441654758984666153073 2807581241069238499614805)
            ·
              refine ⟨32901342668780138667361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2807581241069238499614805 32901342668780138667361)
              ·
                rfl

theorem cell22_2595043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 8].length) (baseStart_2595043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595043 prefixEnd_2595043 := by exact prefixLift 2595043
  have htrace : WordTrace (prefixWord ++ tailWord_2595043) baseStart_2595043 baseEnd_2595043 := by
    simpa [prefixWord, tailWord_2595043, baseEnd_2595043] using wordTrace_append hprefix tailTrace_2595043
  have hstable : (prefixWord ++ tailWord_2595043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595043).length < 2 ^ (prefixWord ++ tailWord_2595043).sum := by decide
  have hdescent : baseEnd_2595043 < baseStart_2595043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595071 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 5]
def baseStart_2595071 : Nat := 118140960795 + 2595071 * 2 ^ 59
def prefixEnd_2595071 : Nat := 4983230072969 + 3 ^ 40 * 2595071 * 2
def baseEnd_2595071 : Nat := 296115279009760334772887

theorem tailTrace_2595071 : CollatzResearch.WordTrace tailWord_2595071 prefixEnd_2595071 296115279009760334772887 := by
  unfold tailWord_2595071
  simp only [CollatzResearch.WordTrace]
  refine ⟨94650015181508444686729067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63100010121005629791152711 94650015181508444686729067)
  ·
    refine ⟨141975022772262667030093601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94650015181508444686729067 141975022772262667030093601)
    ·
      refine ⟨106481267079197000272570201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141975022772262667030093601 106481267079197000272570201)
      ·
        refine ⟨79860950309397750204427651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106481267079197000272570201 79860950309397750204427651)
        ·
          refine ⟨119791425464096625306641477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79860950309397750204427651 119791425464096625306641477)
          ·
            refine ⟨22460892274518117244995277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119791425464096625306641477 22460892274518117244995277)
            ·
              refine ⟨8422834602944293966873229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22460892274518117244995277 8422834602944293966873229)
              ·
                refine ⟨3158562976104110237577461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8422834602944293966873229 3158562976104110237577461)
                ·
                  refine ⟨296115279009760334772887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3158562976104110237577461 296115279009760334772887)
                  ·
                    rfl

theorem cell22_2595071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 5].length) (baseStart_2595071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595071 prefixEnd_2595071 := by exact prefixLift 2595071
  have htrace : WordTrace (prefixWord ++ tailWord_2595071) baseStart_2595071 baseEnd_2595071 := by
    simpa [prefixWord, tailWord_2595071, baseEnd_2595071] using wordTrace_append hprefix tailTrace_2595071
  have hstable : (prefixWord ++ tailWord_2595071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595071).length < 2 ^ (prefixWord ++ tailWord_2595071).sum := by decide
  have hdescent : baseEnd_2595071 < baseStart_2595071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595109 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_2595109 : Nat := 118140960795 + 2595109 * 2 ^ 59
def prefixEnd_2595109 : Nat := 4983230072969 + 3 ^ 40 * 2595109 * 2
def baseEnd_2595109 : Nat := 888358845205861571868545

theorem tailTrace_2595109 : CollatzResearch.WordTrace tailWord_2595109 prefixEnd_2595109 888358845205861571868545 := by
  unfold tailWord_2595109
  simp only [CollatzResearch.WordTrace]
  refine ⟨94651401155370777176612381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63100934103580518117741587 94651401155370777176612381)
  ·
    refine ⟨35494275433264041441229643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94651401155370777176612381 35494275433264041441229643)
    ·
      refine ⟨53241413149896062161844465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35494275433264041441229643 53241413149896062161844465)
      ·
        refine ⟨39931059862422046621383349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53241413149896062161844465 39931059862422046621383349)
        ·
          refine ⟨3743536862102066870754689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39931059862422046621383349 3743536862102066870754689)
          ·
            refine ⟨2807652646576550153066017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743536862102066870754689 2807652646576550153066017)
            ·
              refine ⟨2105739484932412614799513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807652646576550153066017 2105739484932412614799513)
              ·
                refine ⟨1579304613699309461099635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105739484932412614799513 1579304613699309461099635)
                ·
                  refine ⟨2368956920548964191649453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579304613699309461099635 2368956920548964191649453)
                  ·
                    refine ⟨888358845205861571868545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368956920548964191649453 888358845205861571868545)
                    ·
                      rfl

theorem cell22_2595109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_2595109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595109 prefixEnd_2595109 := by exact prefixLift 2595109
  have htrace : WordTrace (prefixWord ++ tailWord_2595109) baseStart_2595109 baseEnd_2595109 := by
    simpa [prefixWord, tailWord_2595109, baseEnd_2595109] using wordTrace_append hprefix tailTrace_2595109
  have hstable : (prefixWord ++ tailWord_2595109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595109).length < 2 ^ (prefixWord ++ tailWord_2595109).sum := by decide
  have hdescent : baseEnd_2595109 < baseStart_2595109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595148 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_2595148 : Nat := 118140960795 + 2595148 * 2 ^ 59
def prefixEnd_2595148 : Nat := 4983230072969 + 3 ^ 40 * 2595148 * 2
def baseEnd_2595148 : Nat := 888372195702878470143425

theorem tailTrace_2595148 : CollatzResearch.WordTrace tailWord_2595148 prefixEnd_2595148 888372195702878470143425 := by
  unfold tailWord_2595148
  simp only [CollatzResearch.WordTrace]
  refine ⟨47326411801114743418641049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63101882401486324558188065 47326411801114743418641049)
  ·
    refine ⟨35494808850836057563980787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47326411801114743418641049 35494808850836057563980787)
    ·
      refine ⟨53242213276254086345971181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35494808850836057563980787 53242213276254086345971181)
      ·
        refine ⟨19965829978595282379739193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53242213276254086345971181 19965829978595282379739193)
        ·
          refine ⟨14974372483946461784804395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19965829978595282379739193 14974372483946461784804395)
          ·
            refine ⟨22461558725919692677206593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14974372483946461784804395 22461558725919692677206593)
            ·
              refine ⟨16846169044439769507904945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22461558725919692677206593 16846169044439769507904945)
              ·
                refine ⟨12634626783329827130928709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16846169044439769507904945 12634626783329827130928709)
                ·
                  refine ⟨2368992521874342587049133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12634626783329827130928709 2368992521874342587049133)
                  ·
                    refine ⟨888372195702878470143425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368992521874342587049133 888372195702878470143425)
                    ·
                      rfl

theorem cell22_2595148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_2595148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595148 prefixEnd_2595148 := by exact prefixLift 2595148
  have htrace : WordTrace (prefixWord ++ tailWord_2595148) baseStart_2595148 baseEnd_2595148 := by
    simpa [prefixWord, tailWord_2595148, baseEnd_2595148] using wordTrace_append hprefix tailTrace_2595148
  have hstable : (prefixWord ++ tailWord_2595148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595148).length < 2 ^ (prefixWord ++ tailWord_2595148).sum := by decide
  have hdescent : baseEnd_2595148 < baseStart_2595148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595283 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 10, 3]
def baseStart_2595283 : Nat := 118140960795 + 2595283 * 2 ^ 59
def prefixEnd_2595283 : Nat := 4983230072969 + 3 ^ 40 * 2595283 * 2
def baseEnd_2595283 : Nat := 888418408961783118018011

theorem tailTrace_2595283 : CollatzResearch.WordTrace tailWord_2595283 prefixEnd_2595283 888418408961783118018011 := by
  unfold tailWord_2595283
  simp only [CollatzResearch.WordTrace]
  refine ⟨94657747456740404893446503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63105164971160269928964335 94657747456740404893446503)
  ·
    refine ⟨141986621185110607340169755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94657747456740404893446503 141986621185110607340169755)
    ·
      refine ⟨212979931777665911010254633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141986621185110607340169755 212979931777665911010254633)
      ·
        refine ⟨159734948833249433257690975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212979931777665911010254633 159734948833249433257690975)
        ·
          refine ⟨239602423249874149886536463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159734948833249433257690975 239602423249874149886536463)
          ·
            refine ⟨359403634874811224829804695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239602423249874149886536463 359403634874811224829804695)
            ·
              refine ⟨539105452312216837244707043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359403634874811224829804695 539105452312216837244707043)
              ·
                refine ⟨808658178468325255867060565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539105452312216837244707043 808658178468325255867060565)
                ·
                  refine ⟨2369115757231421648048029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 808658178468325255867060565 2369115757231421648048029)
                  ·
                    refine ⟨888418408961783118018011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369115757231421648048029 888418408961783118018011)
                    ·
                      rfl

theorem cell22_2595283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 3].length) (baseStart_2595283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595283 prefixEnd_2595283 := by exact prefixLift 2595283
  have htrace : WordTrace (prefixWord ++ tailWord_2595283) baseStart_2595283 baseEnd_2595283 := by
    simpa [prefixWord, tailWord_2595283, baseEnd_2595283] using wordTrace_append hprefix tailTrace_2595283
  have hstable : (prefixWord ++ tailWord_2595283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595283).length < 2 ^ (prefixWord ++ tailWord_2595283).sum := by decide
  have hdescent : baseEnd_2595283 < baseStart_2595283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595351 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 2, 3]
def baseStart_2595351 : Nat := 118140960795 + 2595351 * 2 ^ 59
def prefixEnd_2595351 : Nat := 4983230072969 + 3 ^ 40 * 2595351 * 2
def baseEnd_2595351 : Nat := 888441686751453607317803

theorem tailTrace_2595351 : CollatzResearch.WordTrace tailWord_2595351 prefixEnd_2595351 888441686751453607317803 := by
  unfold tailWord_2595351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94660227620494052506921907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63106818413662701671281271 94660227620494052506921907)
  ·
    refine ⟨141990341430741078760382861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94660227620494052506921907 141990341430741078760382861)
    ·
      refine ⟨53246378036527904535143573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141990341430741078760382861 53246378036527904535143573)
      ·
        refine ⟨2495923970462245525084855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53246378036527904535143573 2495923970462245525084855)
        ·
          refine ⟨3743885955693368287627283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495923970462245525084855 3743885955693368287627283)
          ·
            refine ⟨5615828933540052431440925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743885955693368287627283 5615828933540052431440925)
            ·
              refine ⟨2105935850077519661790347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5615828933540052431440925 2105935850077519661790347)
              ·
                refine ⟨3158903775116279492685521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105935850077519661790347 3158903775116279492685521)
                ·
                  refine ⟨2369177831337209619514141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3158903775116279492685521 2369177831337209619514141)
                  ·
                    refine ⟨888441686751453607317803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369177831337209619514141 888441686751453607317803)
                    ·
                      rfl

theorem cell22_2595351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_2595351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595351 prefixEnd_2595351 := by exact prefixLift 2595351
  have htrace : WordTrace (prefixWord ++ tailWord_2595351) baseStart_2595351 baseEnd_2595351 := by
    simpa [prefixWord, tailWord_2595351, baseEnd_2595351] using wordTrace_append hprefix tailTrace_2595351
  have hstable : (prefixWord ++ tailWord_2595351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595351).length < 2 ^ (prefixWord ++ tailWord_2595351).sum := by decide
  have hdescent : baseEnd_2595351 < baseStart_2595351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595364 : List Nat := [2, 3, 1, 5, 1, 2, 2, 6]
def baseStart_2595364 : Nat := 118140960795 + 2595364 * 2 ^ 59
def prefixEnd_2595364 : Nat := 4983230072969 + 3 ^ 40 * 2595364 * 2
def baseEnd_2595364 : Nat := 98716237435236211860307

theorem tailTrace_2595364 : CollatzResearch.WordTrace tailWord_2595364 prefixEnd_2595364 98716237435236211860307 := by
  unfold tailWord_2595364
  simp only [CollatzResearch.WordTrace]
  refine ⟨47330350884723477863572573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63107134512964637151430097 47330350884723477863572573)
  ·
    refine ⟨17748881581771304198839715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47330350884723477863572573 17748881581771304198839715)
    ·
      refine ⟨26623322372656956298259573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17748881581771304198839715 26623322372656956298259573)
      ·
        refine ⟨2495936472436589652961835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26623322372656956298259573 2495936472436589652961835)
        ·
          refine ⟨3743904708654884479442753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495936472436589652961835 3743904708654884479442753)
          ·
            refine ⟨2807928531491163359582065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743904708654884479442753 2807928531491163359582065)
            ·
              refine ⟨2105946398618372519686549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807928531491163359582065 2105946398618372519686549)
              ·
                refine ⟨98716237435236211860307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2105946398618372519686549 98716237435236211860307)
                ·
                  rfl

theorem cell22_2595364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 6].length) (baseStart_2595364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595364 prefixEnd_2595364 := by exact prefixLift 2595364
  have htrace : WordTrace (prefixWord ++ tailWord_2595364) baseStart_2595364 baseEnd_2595364 := by
    simpa [prefixWord, tailWord_2595364, baseEnd_2595364] using wordTrace_append hprefix tailTrace_2595364
  have hstable : (prefixWord ++ tailWord_2595364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595364).length < 2 ^ (prefixWord ++ tailWord_2595364).sum := by decide
  have hdescent : baseEnd_2595364 < baseStart_2595364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595435 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 4, 3]
def baseStart_2595435 : Nat := 118140960795 + 2595435 * 2 ^ 59
def prefixEnd_2595435 : Nat := 4983230072969 + 3 ^ 40 * 2595435 * 2
def baseEnd_2595435 : Nat := 888470441668105388217545

theorem tailTrace_2595435 : CollatzResearch.WordTrace tailWord_2595435 prefixEnd_2595435 888470441668105388217545 := by
  unfold tailWord_2595435
  simp only [CollatzResearch.WordTrace]
  refine ⟨94663291352189734852979759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63108860901459823235319839 94663291352189734852979759)
  ·
    refine ⟨141994937028284602279469639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94663291352189734852979759 141994937028284602279469639)
    ·
      refine ⟨212992405542426903419204459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141994937028284602279469639 212992405542426903419204459)
      ·
        refine ⟨319488608313640355128806689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212992405542426903419204459 319488608313640355128806689)
        ·
          refine ⟨239616456235230266346605017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319488608313640355128806689 239616456235230266346605017)
          ·
            refine ⟨179712342176422699759953763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239616456235230266346605017 179712342176422699759953763)
            ·
              refine ⟨269568513264634049639930645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179712342176422699759953763 269568513264634049639930645)
              ·
                refine ⟨12636024059279721076871749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 269568513264634049639930645 12636024059279721076871749)
                ·
                  refine ⟨2369254511114947701913453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12636024059279721076871749 2369254511114947701913453)
                  ·
                    refine ⟨888470441668105388217545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369254511114947701913453 888470441668105388217545)
                    ·
                      rfl

theorem cell22_2595435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 3].length) (baseStart_2595435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595435 prefixEnd_2595435 := by exact prefixLift 2595435
  have htrace : WordTrace (prefixWord ++ tailWord_2595435) baseStart_2595435 baseEnd_2595435 := by
    simpa [prefixWord, tailWord_2595435, baseEnd_2595435] using wordTrace_append hprefix tailTrace_2595435
  have hstable : (prefixWord ++ tailWord_2595435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595435).length < 2 ^ (prefixWord ++ tailWord_2595435).sum := by decide
  have hdescent : baseEnd_2595435 < baseStart_2595435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595452 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_2595452 : Nat := 118140960795 + 2595452 * 2 ^ 59
def prefixEnd_2595452 : Nat := 4983230072969 + 3 ^ 40 * 2595452 * 2
def baseEnd_2595452 : Nat := 888476261115523010542493

theorem tailTrace_2595452 : CollatzResearch.WordTrace tailWord_2595452 prefixEnd_2595452 888476261115523010542493 := by
  unfold tailWord_2595452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47331955696564073378174305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63109274262085431170899073 47331955696564073378174305)
  ·
    refine ⟨35498966772423055033630729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47331955696564073378174305 35498966772423055033630729)
    ·
      refine ⟨26624225079317291275223047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35498966772423055033630729 26624225079317291275223047)
      ·
        refine ⟨39936337618975936912834571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26624225079317291275223047 39936337618975936912834571)
        ·
          refine ⟨59904506428463905369251857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39936337618975936912834571 59904506428463905369251857)
          ·
            refine ⟨44928379821347929026938893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59904506428463905369251857 44928379821347929026938893)
            ·
              refine ⟨16848142433005473385102085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44928379821347929026938893 16848142433005473385102085)
              ·
                refine ⟨3159026706188526259706641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16848142433005473385102085 3159026706188526259706641)
                ·
                  refine ⟨2369270029641394694779981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159026706188526259706641 2369270029641394694779981)
                  ·
                    refine ⟨888476261115523010542493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369270029641394694779981 888476261115523010542493)
                    ·
                      rfl

theorem cell22_2595452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_2595452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595452 prefixEnd_2595452 := by exact prefixLift 2595452
  have htrace : WordTrace (prefixWord ++ tailWord_2595452) baseStart_2595452 baseEnd_2595452 := by
    simpa [prefixWord, tailWord_2595452, baseEnd_2595452] using wordTrace_append hprefix tailTrace_2595452
  have hstable : (prefixWord ++ tailWord_2595452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595452).length < 2 ^ (prefixWord ++ tailWord_2595452).sum := by decide
  have hdescent : baseEnd_2595452 < baseStart_2595452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595484 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_2595484 : Nat := 118140960795 + 2595484 * 2 ^ 59
def prefixEnd_2595484 : Nat := 4983230072969 + 3 ^ 40 * 2595484 * 2
def baseEnd_2595484 : Nat := 888487215369485593742395

theorem tailTrace_2595484 : CollatzResearch.WordTrace tailWord_2595484 prefixEnd_2595484 888487215369485593742395 := by
  unfold tailWord_2595484
  simp only [CollatzResearch.WordTrace]
  refine ⟨47332539264506108110756753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63110052352674810814342337 47332539264506108110756753)
  ·
    refine ⟨35499404448379581083067565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47332539264506108110756753 35499404448379581083067565)
    ·
      refine ⟨13312276668142342906150337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35499404448379581083067565 13312276668142342906150337)
      ·
        refine ⟨9984207501106757179612753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13312276668142342906150337 9984207501106757179612753)
        ·
          refine ⟨7488155625830067884709565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9984207501106757179612753 7488155625830067884709565)
          ·
            refine ⟨2808058359686275456766087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7488155625830067884709565 2808058359686275456766087)
            ·
              refine ⟨4212087539529413185149131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808058359686275456766087 4212087539529413185149131)
              ·
                refine ⟨6318131309294119777723697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4212087539529413185149131 6318131309294119777723697)
                ·
                  refine ⟨4738598481970589833292773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6318131309294119777723697 4738598481970589833292773)
                  ·
                    refine ⟨888487215369485593742395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738598481970589833292773 888487215369485593742395)
                    ·
                      rfl

theorem cell22_2595484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_2595484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595484 prefixEnd_2595484 := by exact prefixLift 2595484
  have htrace : WordTrace (prefixWord ++ tailWord_2595484) baseStart_2595484 baseEnd_2595484 := by
    simpa [prefixWord, tailWord_2595484, baseEnd_2595484] using wordTrace_append hprefix tailTrace_2595484
  have hstable : (prefixWord ++ tailWord_2595484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595484).length < 2 ^ (prefixWord ++ tailWord_2595484).sum := by decide
  have hdescent : baseEnd_2595484 < baseStart_2595484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595514 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_2595514 : Nat := 118140960795 + 2595514 * 2 ^ 59
def prefixEnd_2595514 : Nat := 4983230072969 + 3 ^ 40 * 2595514 * 2
def baseEnd_2595514 : Nat := 888497484982575515492303

theorem tailTrace_2595514 : CollatzResearch.WordTrace tailWord_2595514 prefixEnd_2595514 888497484982575515492303 := by
  unfold tailWord_2595514
  simp only [CollatzResearch.WordTrace]
  refine ⟨23666543179725882836276399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63110781812602354230070397 23666543179725882836276399)
  ·
    refine ⟨35499814769588824254414599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23666543179725882836276399 35499814769588824254414599)
    ·
      refine ⟨53249722154383236381621899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35499814769588824254414599 53249722154383236381621899)
      ·
        refine ⟨79874583231574854572432849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53249722154383236381621899 79874583231574854572432849)
        ·
          refine ⟨59905937423681140929324637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79874583231574854572432849 59905937423681140929324637)
          ·
            refine ⟨22464726533880427848496739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59905937423681140929324637 22464726533880427848496739)
            ·
              refine ⟨33697089800820641772745109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22464726533880427848496739 33697089800820641772745109)
              ·
                refine ⟨1579551084413467583097427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33697089800820641772745109 1579551084413467583097427)
                ·
                  refine ⟨2369326626620201374646141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579551084413467583097427 2369326626620201374646141)
                  ·
                    refine ⟨888497484982575515492303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369326626620201374646141 888497484982575515492303)
                    ·
                      rfl

theorem cell22_2595514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_2595514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595514 prefixEnd_2595514 := by exact prefixLift 2595514
  have htrace : WordTrace (prefixWord ++ tailWord_2595514) baseStart_2595514 baseEnd_2595514 := by
    simpa [prefixWord, tailWord_2595514, baseEnd_2595514] using wordTrace_append hprefix tailTrace_2595514
  have hstable : (prefixWord ++ tailWord_2595514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595514).length < 2 ^ (prefixWord ++ tailWord_2595514).sum := by decide
  have hdescent : baseEnd_2595514 < baseStart_2595514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595533 : List Nat := [1, 6, 2, 1, 3, 1, 2, 6]
def baseStart_2595533 : Nat := 118140960795 + 2595533 * 2 ^ 59
def prefixEnd_2595533 : Nat := 4983230072969 + 3 ^ 40 * 2595533 * 2
def baseEnd_2595533 : Nat := 98722665452318422140805

theorem tailTrace_2595533 : CollatzResearch.WordTrace tailWord_2595533 prefixEnd_2595533 98722665452318422140805 := by
  unfold tailWord_2595533
  simp only [CollatzResearch.WordTrace]
  refine ⟨94666865705834697590047253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63111243803889798393364835 94666865705834697590047253)
  ·
    refine ⟨4437509329961001449533465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94666865705834697590047253 4437509329961001449533465)
    ·
      refine ⟨3328131997470751087150099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4437509329961001449533465 3328131997470751087150099)
      ·
        refine ⟨4992197996206126630725149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328131997470751087150099 4992197996206126630725149)
        ·
          refine ⟨1872074248577297486521931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4992197996206126630725149 1872074248577297486521931)
          ·
            refine ⟨2808111372865946229782897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872074248577297486521931 2808111372865946229782897)
            ·
              refine ⟨2106083529649459672337173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808111372865946229782897 2106083529649459672337173)
              ·
                refine ⟨98722665452318422140805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2106083529649459672337173 98722665452318422140805)
                ·
                  rfl

theorem cell22_2595533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 6].length) (baseStart_2595533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595533 prefixEnd_2595533 := by exact prefixLift 2595533
  have htrace : WordTrace (prefixWord ++ tailWord_2595533) baseStart_2595533 baseEnd_2595533 := by
    simpa [prefixWord, tailWord_2595533, baseEnd_2595533] using wordTrace_append hprefix tailTrace_2595533
  have hstable : (prefixWord ++ tailWord_2595533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595533).length < 2 ^ (prefixWord ++ tailWord_2595533).sum := by decide
  have hdescent : baseEnd_2595533 < baseStart_2595533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595548 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2595548 : Nat := 118140960795 + 2595548 * 2 ^ 59
def prefixEnd_2595548 : Nat := 4983230072969 + 3 ^ 40 * 2595548 * 2
def baseEnd_2595548 : Nat := 888509123877410760142199

theorem tailTrace_2595548 : CollatzResearch.WordTrace tailWord_2595548 prefixEnd_2595548 888509123877410760142199 := by
  unfold tailWord_2595548
  simp only [CollatzResearch.WordTrace]
  refine ⟨47333706400390177575921649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63111608533853570101228865 47333706400390177575921649)
  ·
    refine ⟨35500279800292633181941237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47333706400390177575921649 35500279800292633181941237)
    ·
      refine ⟨3328151231277434360806991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35500279800292633181941237 3328151231277434360806991)
      ·
        refine ⟨4992226846916151541210487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328151231277434360806991 4992226846916151541210487)
        ·
          refine ⟨7488340270374227311815731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992226846916151541210487 7488340270374227311815731)
          ·
            refine ⟨11232510405561340967723597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7488340270374227311815731 11232510405561340967723597)
            ·
              refine ⟨4212191402085502862896349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11232510405561340967723597 4212191402085502862896349)
              ·
                refine ⟨1579571775782063573586131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4212191402085502862896349 1579571775782063573586131)
                ·
                  refine ⟨2369357663673095360379197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579571775782063573586131 2369357663673095360379197)
                  ·
                    refine ⟨888509123877410760142199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369357663673095360379197 888509123877410760142199)
                    ·
                      rfl

theorem cell22_2595548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2595548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595548 prefixEnd_2595548 := by exact prefixLift 2595548
  have htrace : WordTrace (prefixWord ++ tailWord_2595548) baseStart_2595548 baseEnd_2595548 := by
    simpa [prefixWord, tailWord_2595548, baseEnd_2595548] using wordTrace_append hprefix tailTrace_2595548
  have hstable : (prefixWord ++ tailWord_2595548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595548).length < 2 ^ (prefixWord ++ tailWord_2595548).sum := by decide
  have hdescent : baseEnd_2595548 < baseStart_2595548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595591 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 1, 4]
def baseStart_2595591 : Nat := 118140960795 + 2595591 * 2 ^ 59
def prefixEnd_2595591 : Nat := 4983230072969 + 3 ^ 40 * 2595591 * 2
def baseEnd_2595591 : Nat := 888523843656172981317067

theorem tailTrace_2595591 : CollatzResearch.WordTrace tailWord_2595591 prefixEnd_2595591 888523843656172981317067 := by
  unfold tailWord_2595591
  simp only [CollatzResearch.WordTrace]
  refine ⟨94668981139624573495658627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63112654093083048997105751 94668981139624573495658627)
  ·
    refine ⟨142003471709436860243487941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94668981139624573495658627 142003471709436860243487941)
    ·
      refine ⟨26625650945519411295653989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142003471709436860243487941 26625650945519411295653989)
      ·
        refine ⟨4992309552284889617935123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26625650945519411295653989 4992309552284889617935123)
        ·
          refine ⟨7488464328427334426902685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992309552284889617935123 7488464328427334426902685)
          ·
            refine ⟨2808174123160250410088507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7488464328427334426902685 2808174123160250410088507)
            ·
              refine ⟨4212261184740375615132761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808174123160250410088507 4212261184740375615132761)
              ·
                refine ⟨3159195888555281711349571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212261184740375615132761 3159195888555281711349571)
                ·
                  refine ⟨4738793832832922567024357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159195888555281711349571 4738793832832922567024357)
                  ·
                    refine ⟨888523843656172981317067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738793832832922567024357 888523843656172981317067)
                    ·
                      rfl

theorem cell22_2595591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_2595591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595591 prefixEnd_2595591 := by exact prefixLift 2595591
  have htrace : WordTrace (prefixWord ++ tailWord_2595591) baseStart_2595591 baseEnd_2595591 := by
    simpa [prefixWord, tailWord_2595591, baseEnd_2595591] using wordTrace_append hprefix tailTrace_2595591
  have hstable : (prefixWord ++ tailWord_2595591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595591).length < 2 ^ (prefixWord ++ tailWord_2595591).sum := by decide
  have hdescent : baseEnd_2595591 < baseStart_2595591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595632 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_2595632 : Nat := 118140960795 + 2595632 * 2 ^ 59
def prefixEnd_2595632 : Nat := 4983230072969 + 3 ^ 40 * 2595632 * 2
def baseEnd_2595632 : Nat := 888537878794062541041941

theorem tailTrace_2595632 : CollatzResearch.WordTrace tailWord_2595632 prefixEnd_2595632 888537878794062541041941 := by
  unfold tailWord_2595632
  simp only [CollatzResearch.WordTrace]
  refine ⟨47335238266238018748950575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63113651021650691665267433 47335238266238018748950575)
  ·
    refine ⟨71002857399357028123425863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47335238266238018748950575 71002857399357028123425863)
    ·
      refine ⟨106504286099035542185138795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71002857399357028123425863 106504286099035542185138795)
      ·
        refine ⟨159756429148553313277708193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106504286099035542185138795 159756429148553313277708193)
        ·
          refine ⟨119817321861414984958281145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159756429148553313277708193 119817321861414984958281145)
          ·
            refine ⟨89862991396061238718710859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119817321861414984958281145 89862991396061238718710859)
            ·
              refine ⟨134794487094091858078066289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89862991396061238718710859 134794487094091858078066289)
              ·
                refine ⟨101095865320568893558549717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134794487094091858078066289 101095865320568893558549717)
                ·
                  refine ⟨2369434343450833442778509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101095865320568893558549717 2369434343450833442778509)
                  ·
                    refine ⟨888537878794062541041941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369434343450833442778509 888537878794062541041941)
                    ·
                      rfl

theorem cell22_2595632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_2595632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595632 prefixEnd_2595632 := by exact prefixLift 2595632
  have htrace : WordTrace (prefixWord ++ tailWord_2595632) baseStart_2595632 baseEnd_2595632 := by
    simpa [prefixWord, tailWord_2595632, baseEnd_2595632] using wordTrace_append hprefix tailTrace_2595632
  have hstable : (prefixWord ++ tailWord_2595632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595632).length < 2 ^ (prefixWord ++ tailWord_2595632).sum := by decide
  have hdescent : baseEnd_2595632 < baseStart_2595632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595707 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 6]
def baseStart_2595707 : Nat := 118140960795 + 2595707 * 2 ^ 59
def prefixEnd_2595707 : Nat := 4983230072969 + 3 ^ 40 * 2595707 * 2
def baseEnd_2595707 : Nat := 296187850942262448472237

theorem tailTrace_2595707 : CollatzResearch.WordTrace tailWord_2595707 prefixEnd_2595707 296187850942262448472237 := by
  unfold tailWord_2595707
  simp only [CollatzResearch.WordTrace]
  refine ⟨94673212007204325306881375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63115474671469550204587583 94673212007204325306881375)
  ·
    refine ⟨142009818010806487960322063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94673212007204325306881375 142009818010806487960322063)
    ·
      refine ⟨213014727016209731940483095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142009818010806487960322063 213014727016209731940483095)
      ·
        refine ⟨319522090524314597910724643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213014727016209731940483095 319522090524314597910724643)
        ·
          refine ⟨479283135786471896866086965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319522090524314597910724643 479283135786471896866086965)
          ·
            refine ⟨44932793979981740331195653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 479283135786471896866086965 44932793979981740331195653)
            ·
              refine ⟨8424898871246576312099185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44932793979981740331195653 8424898871246576312099185)
              ·
                refine ⟨6318674153434932234074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8424898871246576312099185 6318674153434932234074389)
                ·
                  refine ⟨296187850942262448472237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6318674153434932234074389 296187850942262448472237)
                  ·
                    rfl

theorem cell22_2595707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_2595707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595707 prefixEnd_2595707 := by exact prefixLift 2595707
  have htrace : WordTrace (prefixWord ++ tailWord_2595707) baseStart_2595707 baseEnd_2595707 := by
    simpa [prefixWord, tailWord_2595707, baseEnd_2595707] using wordTrace_append hprefix tailTrace_2595707
  have hstable : (prefixWord ++ tailWord_2595707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595707).length < 2 ^ (prefixWord ++ tailWord_2595707).sum := by decide
  have hdescent : baseEnd_2595707 < baseStart_2595707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595709 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_2595709 : Nat := 118140960795 + 2595709 * 2 ^ 59
def prefixEnd_2595709 : Nat := 4983230072969 + 3 ^ 40 * 2595709 * 2
def baseEnd_2595709 : Nat := 888564237467660006866705

theorem tailTrace_2595709 : CollatzResearch.WordTrace tailWord_2595709 prefixEnd_2595709 888564237467660006866705 := by
  unfold tailWord_2595709
  simp only [CollatzResearch.WordTrace]
  refine ⟨94673284953197079648454181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63115523302131386432302787 94673284953197079648454181)
  ·
    refine ⟨17751240928724452434085159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94673284953197079648454181 17751240928724452434085159)
    ·
      refine ⟨26626861393086678651127739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17751240928724452434085159 26626861393086678651127739)
      ·
        refine ⟨39940292089630017976691609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26626861393086678651127739 39940292089630017976691609)
        ·
          refine ⟨29955219067222513482518707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39940292089630017976691609 29955219067222513482518707)
          ·
            refine ⟨44932828600833770223778061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29955219067222513482518707 44932828600833770223778061)
            ·
              refine ⟨16849810725312663833916773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44932828600833770223778061 16849810725312663833916773)
              ·
                refine ⟨3159339510996124468859395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16849810725312663833916773 3159339510996124468859395)
                ·
                  refine ⟨4739009266494186703289093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159339510996124468859395 4739009266494186703289093)
                  ·
                    refine ⟨888564237467660006866705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739009266494186703289093 888564237467660006866705)
                    ·
                      rfl

theorem cell22_2595709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_2595709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595709 prefixEnd_2595709 := by exact prefixLift 2595709
  have htrace : WordTrace (prefixWord ++ tailWord_2595709) baseStart_2595709 baseEnd_2595709 := by
    simpa [prefixWord, tailWord_2595709, baseEnd_2595709] using wordTrace_append hprefix tailTrace_2595709
  have hstable : (prefixWord ++ tailWord_2595709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595709).length < 2 ^ (prefixWord ++ tailWord_2595709).sum := by decide
  have hdescent : baseEnd_2595709 < baseStart_2595709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595734 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2595734 : Nat := 118140960795 + 2595734 * 2 ^ 59
def prefixEnd_2595734 : Nat := 4983230072969 + 3 ^ 40 * 2595734 * 2
def baseEnd_2595734 : Nat := 888572795478568274991629

theorem tailTrace_2595734 : CollatzResearch.WordTrace tailWord_2595734 prefixEnd_2595734 888572795478568274991629 := by
  unfold tailWord_2595734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5917137298631656807382141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63116131185404339278742837 5917137298631656807382141)
  ·
    refine ⟨2218926486986871302768303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5917137298631656807382141 2218926486986871302768303)
    ·
      refine ⟨3328389730480306954152455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2218926486986871302768303 3328389730480306954152455)
      ·
        refine ⟨4992584595720460431228683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328389730480306954152455 4992584595720460431228683)
        ·
          refine ⟨7488876893580690646843025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992584595720460431228683 7488876893580690646843025)
          ·
            refine ⟨5616657670185517985132269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7488876893580690646843025 5616657670185517985132269)
            ·
              refine ⟨2106246626319569244424601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5616657670185517985132269 2106246626319569244424601)
              ·
                refine ⟨1579684969739676933318451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106246626319569244424601 1579684969739676933318451)
                ·
                  refine ⟨2369527454609515399977677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579684969739676933318451 2369527454609515399977677)
                  ·
                    refine ⟨888572795478568274991629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369527454609515399977677 888572795478568274991629)
                    ·
                      rfl

theorem cell22_2595734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2595734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595734 prefixEnd_2595734 := by exact prefixLift 2595734
  have htrace : WordTrace (prefixWord ++ tailWord_2595734) baseStart_2595734 baseEnd_2595734 := by
    simpa [prefixWord, tailWord_2595734, baseEnd_2595734] using wordTrace_append hprefix tailTrace_2595734
  have hstable : (prefixWord ++ tailWord_2595734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595734).length < 2 ^ (prefixWord ++ tailWord_2595734).sum := by decide
  have hdescent : baseEnd_2595734 < baseStart_2595734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595767 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2595767 : Nat := 118140960795 + 2595767 * 2 ^ 59
def prefixEnd_2595767 : Nat := 4983230072969 + 3 ^ 40 * 2595767 * 2
def baseEnd_2595767 : Nat := 888584092052967188916527

theorem tailTrace_2595767 : CollatzResearch.WordTrace tailWord_2595767 prefixEnd_2595767 888584092052967188916527 := by
  unfold tailWord_2595767
  simp only [CollatzResearch.WordTrace]
  refine ⟨94675400386986955554065555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63116933591324637036043703 94675400386986955554065555)
  ·
    refine ⟨142013100580480433331098333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94675400386986955554065555 142013100580480433331098333)
    ·
      refine ⟨53254912717680162499161875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142013100580480433331098333 53254912717680162499161875)
      ·
        refine ⟨79882369076520243748742813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53254912717680162499161875 79882369076520243748742813)
        ·
          refine ⟨29955888403695091405778555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79882369076520243748742813 29955888403695091405778555)
          ·
            refine ⟨44933832605542637108667833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29955888403695091405778555 44933832605542637108667833)
            ·
              refine ⟨33700374454156977831500875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44933832605542637108667833 33700374454156977831500875)
              ·
                refine ⟨50550561681235466747251313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33700374454156977831500875 50550561681235466747251313)
                ·
                  refine ⟨37912921260926600060438485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50550561681235466747251313 37912921260926600060438485)
                  ·
                    refine ⟨888584092052967188916527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37912921260926600060438485 888584092052967188916527)
                    ·
                      rfl

theorem cell22_2595767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2595767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595767 prefixEnd_2595767 := by exact prefixLift 2595767
  have htrace : WordTrace (prefixWord ++ tailWord_2595767) baseStart_2595767 baseEnd_2595767 := by
    simpa [prefixWord, tailWord_2595767, baseEnd_2595767] using wordTrace_append hprefix tailTrace_2595767
  have hstable : (prefixWord ++ tailWord_2595767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595767).length < 2 ^ (prefixWord ++ tailWord_2595767).sum := by decide
  have hdescent : baseEnd_2595767 < baseStart_2595767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595876 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_2595876 : Nat := 118140960795 + 2595876 * 2 ^ 59
def prefixEnd_2595876 : Nat := 4983230072969 + 3 ^ 40 * 2595876 * 2
def baseEnd_2595876 : Nat := 296207134993509079313731

theorem tailTrace_2595876 : CollatzResearch.WordTrace tailWord_2595876 prefixEnd_2595876 296207134993509079313731 := by
  unfold tailWord_2595876
  simp only [CollatzResearch.WordTrace]
  refine ⟨47339687971796033584891741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63119583962394711446522321 47339687971796033584891741)
  ·
    refine ⟨17752382989423512594334403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47339687971796033584891741 17752382989423512594334403)
    ·
      refine ⟨26628574484135268891501605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17752382989423512594334403 26628574484135268891501605)
      ·
        refine ⟨4992857715775362917156551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26628574484135268891501605 4992857715775362917156551)
        ·
          refine ⟨7489286573663044375734827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992857715775362917156551 7489286573663044375734827)
          ·
            refine ⟨11233929860494566563602241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7489286573663044375734827 11233929860494566563602241)
            ·
              refine ⟨8425447395370924922701681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11233929860494566563602241 8425447395370924922701681)
              ·
                refine ⟨6319085546528193692026261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8425447395370924922701681 6319085546528193692026261)
                ·
                  refine ⟨296207134993509079313731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6319085546528193692026261 296207134993509079313731)
                  ·
                    rfl

theorem cell22_2595876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_2595876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595876 prefixEnd_2595876 := by exact prefixLift 2595876
  have htrace : WordTrace (prefixWord ++ tailWord_2595876) baseStart_2595876 baseEnd_2595876 := by
    simpa [prefixWord, tailWord_2595876, baseEnd_2595876] using wordTrace_append hprefix tailTrace_2595876
  have hstable : (prefixWord ++ tailWord_2595876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595876).length < 2 ^ (prefixWord ++ tailWord_2595876).sum := by decide
  have hdescent : baseEnd_2595876 < baseStart_2595876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595889 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2595889 : Nat := 118140960795 + 2595889 * 2 ^ 59
def prefixEnd_2595889 : Nat := 4983230072969 + 3 ^ 40 * 2595889 * 2
def baseEnd_2595889 : Nat := 888625855146199537366153

theorem tailTrace_2595889 : CollatzResearch.WordTrace tailWord_2595889 prefixEnd_2595889 888625855146199537366153 := by
  unfold tailWord_2595889
  simp only [CollatzResearch.WordTrace]
  refine ⟨94679850092544970390006721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63119900061696646926671147 94679850092544970390006721)
  ·
    refine ⟨71009887569408727792505041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94679850092544970390006721 71009887569408727792505041)
    ·
      refine ⟨53257415677056545844378781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71009887569408727792505041 53257415677056545844378781)
      ·
        refine ⟨19971530878896204691642043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53257415677056545844378781 19971530878896204691642043)
        ·
          refine ⟨29957296318344307037463065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19971530878896204691642043 29957296318344307037463065)
          ·
            refine ⟨22467972238758230278097299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29957296318344307037463065 22467972238758230278097299)
            ·
              refine ⟨33701958358137345417145949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22467972238758230278097299 33701958358137345417145949)
              ·
                refine ⟨12638234384301504531429731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33701958358137345417145949 12638234384301504531429731)
                ·
                  refine ⟨18957351576452256797144597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12638234384301504531429731 18957351576452256797144597)
                  ·
                    refine ⟨888625855146199537366153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18957351576452256797144597 888625855146199537366153)
                    ·
                      rfl

theorem cell22_2595889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2595889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595889 prefixEnd_2595889 := by exact prefixLift 2595889
  have htrace : WordTrace (prefixWord ++ tailWord_2595889) baseStart_2595889 baseEnd_2595889 := by
    simpa [prefixWord, tailWord_2595889, baseEnd_2595889] using wordTrace_append hprefix tailTrace_2595889
  have hstable : (prefixWord ++ tailWord_2595889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595889).length < 2 ^ (prefixWord ++ tailWord_2595889).sum := by decide
  have hdescent : baseEnd_2595889 < baseStart_2595889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595910 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2595910 : Nat := 118140960795 + 2595910 * 2 ^ 59
def prefixEnd_2595910 : Nat := 4983230072969 + 3 ^ 40 * 2595910 * 2
def baseEnd_2595910 : Nat := 296211014625120827530363

theorem tailTrace_2595910 : CollatzResearch.WordTrace tailWord_2595910 prefixEnd_2595910 296211014625120827530363 := by
  unfold tailWord_2595910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958769250795902843016287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63120410683645927317680789 2958769250795902843016287)
  ·
    refine ⟨4438153876193854264524431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2958769250795902843016287 4438153876193854264524431)
    ·
      refine ⟨6657230814290781396786647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4438153876193854264524431 6657230814290781396786647)
      ·
        refine ⟨9985846221436172095179971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6657230814290781396786647 9985846221436172095179971)
        ·
          refine ⟨14978769332154258142769957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9985846221436172095179971 14978769332154258142769957)
          ·
            refine ⟨2808519249778923401769367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14978769332154258142769957 2808519249778923401769367)
            ·
              refine ⟨4212778874668385102654051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808519249778923401769367 4212778874668385102654051)
              ·
                refine ⟨6319168312002577653981077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4212778874668385102654051 6319168312002577653981077)
                ·
                  refine ⟨296211014625120827530363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6319168312002577653981077 296211014625120827530363)
                  ·
                    rfl

theorem cell22_2595910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2595910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595910 prefixEnd_2595910 := by exact prefixLift 2595910
  have htrace : WordTrace (prefixWord ++ tailWord_2595910) baseStart_2595910 baseEnd_2595910 := by
    simpa [prefixWord, tailWord_2595910, baseEnd_2595910] using wordTrace_append hprefix tailTrace_2595910
  have hstable : (prefixWord ++ tailWord_2595910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595910).length < 2 ^ (prefixWord ++ tailWord_2595910).sum := by decide
  have hdescent : baseEnd_2595910 < baseStart_2595910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2595936 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_2595936 : Nat := 118140960795 + 2595936 * 2 ^ 59
def prefixEnd_2595936 : Nat := 4983230072969 + 3 ^ 40 * 2595936 * 2
def baseEnd_2595936 : Nat := 888641944206707081441009

theorem tailTrace_2595936 : CollatzResearch.WordTrace tailWord_2595936 prefixEnd_2595936 888641944206707081441009 := by
  unfold tailWord_2595936
  simp only [CollatzResearch.WordTrace]
  refine ⟨47340782161687348708483831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63121042882249798277978441 47340782161687348708483831)
  ·
    refine ⟨71011173242531023062725747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47340782161687348708483831 71011173242531023062725747)
    ·
      refine ⟨106516759863796534594088621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71011173242531023062725747 106516759863796534594088621)
      ·
        refine ⟨39943784948923700472783233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106516759863796534594088621 39943784948923700472783233)
        ·
          refine ⟨29957838711692775354587425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39943784948923700472783233 29957838711692775354587425)
          ·
            refine ⟨22468379033769581515940569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29957838711692775354587425 22468379033769581515940569)
            ·
              refine ⟨16851284275327186136955427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22468379033769581515940569 16851284275327186136955427)
              ·
                refine ⟨25276926412990779205433141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16851284275327186136955427 25276926412990779205433141)
                ·
                  refine ⟨2369711851217885550509357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25276926412990779205433141 2369711851217885550509357)
                  ·
                    refine ⟨888641944206707081441009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369711851217885550509357 888641944206707081441009)
                    ·
                      rfl

theorem cell22_2595936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_2595936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2595936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2595936 prefixEnd_2595936 := by exact prefixLift 2595936
  have htrace : WordTrace (prefixWord ++ tailWord_2595936) baseStart_2595936 baseEnd_2595936 := by
    simpa [prefixWord, tailWord_2595936, baseEnd_2595936] using wordTrace_append hprefix tailTrace_2595936
  have hstable : (prefixWord ++ tailWord_2595936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2595936).length < 2 ^ (prefixWord ++ tailWord_2595936).sum := by decide
  have hdescent : baseEnd_2595936 < baseStart_2595936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2595936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596028 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_2596028 : Nat := 118140960795 + 2596028 * 2 ^ 59
def prefixEnd_2596028 : Nat := 4983230072969 + 3 ^ 40 * 2596028 * 2
def baseEnd_2596028 : Nat := 296224479228949836046909

theorem tailTrace_2596028 : CollatzResearch.WordTrace tailWord_2596028 prefixEnd_2596028 296224479228949836046909 := by
  unfold tailWord_2596028
  simp only [CollatzResearch.WordTrace]
  refine ⟨47342459919520698564658369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63123279892694264752877825 47342459919520698564658369)
  ·
    refine ⟨35506844939640523923493777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47342459919520698564658369 35506844939640523923493777)
    ·
      refine ⟨26630133704730392942620333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35506844939640523923493777 26630133704730392942620333)
      ·
        refine ⟨9986300139273897353482625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26630133704730392942620333 9986300139273897353482625)
        ·
          refine ⟨7489725104455423015111969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9986300139273897353482625 7489725104455423015111969)
          ·
            refine ⟨5617293828341567261333977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7489725104455423015111969 5617293828341567261333977)
            ·
              refine ⟨4212970371256175446000483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617293828341567261333977 4212970371256175446000483)
              ·
                refine ⟨6319455556884263169000725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4212970371256175446000483 6319455556884263169000725)
                ·
                  refine ⟨296224479228949836046909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6319455556884263169000725 296224479228949836046909)
                  ·
                    rfl

theorem cell22_2596028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_2596028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596028 prefixEnd_2596028 := by exact prefixLift 2596028
  have htrace : WordTrace (prefixWord ++ tailWord_2596028) baseStart_2596028 baseEnd_2596028 := by
    simpa [prefixWord, tailWord_2596028, baseEnd_2596028] using wordTrace_append hprefix tailTrace_2596028
  have hstable : (prefixWord ++ tailWord_2596028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596028).length < 2 ^ (prefixWord ++ tailWord_2596028).sum := by decide
  have hdescent : baseEnd_2596028 < baseStart_2596028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596034 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2596034 : Nat := 118140960795 + 2596034 * 2 ^ 59
def prefixEnd_2596034 : Nat := 4983230072969 + 3 ^ 40 * 2596034 * 2
def baseEnd_2596034 : Nat := 296225163869822497496903

theorem tailTrace_2596034 : CollatzResearch.WordTrace tailWord_2596034 prefixEnd_2596034 296225163869822497496903 := by
  unfold tailWord_2596034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23671284669254915038508789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63123425784679773436023437 23671284669254915038508789)
  ·
    refine ⟨2219182937742648284860199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23671284669254915038508789 2219182937742648284860199)
    ·
      refine ⟨3328774406613972427290299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2219182937742648284860199 3328774406613972427290299)
      ·
        refine ⟨4993161609920958640935449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328774406613972427290299 4993161609920958640935449)
        ·
          refine ⟨3744871207440718980701587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4993161609920958640935449 3744871207440718980701587)
          ·
            refine ⟨5617306811161078471052381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744871207440718980701587 5617306811161078471052381)
            ·
              refine ⟨2106490054185404426644643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5617306811161078471052381 2106490054185404426644643)
              ·
                refine ⟨3159735081278106639966965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106490054185404426644643 3159735081278106639966965)
                ·
                  refine ⟨296225163869822497496903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3159735081278106639966965 296225163869822497496903)
                  ·
                    rfl

theorem cell22_2596034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2596034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596034 prefixEnd_2596034 := by exact prefixLift 2596034
  have htrace : WordTrace (prefixWord ++ tailWord_2596034) baseStart_2596034 baseEnd_2596034 := by
    simpa [prefixWord, tailWord_2596034, baseEnd_2596034] using wordTrace_append hprefix tailTrace_2596034
  have hstable : (prefixWord ++ tailWord_2596034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596034).length < 2 ^ (prefixWord ++ tailWord_2596034).sum := by decide
  have hdescent : baseEnd_2596034 < baseStart_2596034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596094 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2596094 : Nat := 118140960795 + 2596094 * 2 ^ 59
def prefixEnd_2596094 : Nat := 4983230072969 + 3 ^ 40 * 2596094 * 2
def baseEnd_2596094 : Nat := 888696030835647335990525

theorem tailTrace_2596094 : CollatzResearch.WordTrace tailWord_2596094 prefixEnd_2596094 888696030835647335990525 := by
  unfold tailWord_2596094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835915882100286300152417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63124884704534860267479557 11835915882100286300152417)
  ·
    refine ⟨8876936911575214725114313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11835915882100286300152417 8876936911575214725114313)
    ·
      refine ⟨6657702683681411043835735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8876936911575214725114313 6657702683681411043835735)
      ·
        refine ⟨9986554025522116565753603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6657702683681411043835735 9986554025522116565753603)
        ·
          refine ⟨14979831038283174848630405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9986554025522116565753603 14979831038283174848630405)
          ·
            refine ⟨2808718319678095284118201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14979831038283174848630405 2808718319678095284118201)
            ·
              refine ⟨2106538739758571463088651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808718319678095284118201 2106538739758571463088651)
              ·
                refine ⟨3159808109637857194632977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106538739758571463088651 3159808109637857194632977)
                ·
                  refine ⟨2369856082228392895974733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159808109637857194632977 2369856082228392895974733)
                  ·
                    refine ⟨888696030835647335990525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369856082228392895974733 888696030835647335990525)
                    ·
                      rfl

theorem cell22_2596094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2596094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596094 prefixEnd_2596094 := by exact prefixLift 2596094
  have htrace : WordTrace (prefixWord ++ tailWord_2596094) baseStart_2596094 baseEnd_2596094 := by
    simpa [prefixWord, tailWord_2596094, baseEnd_2596094] using wordTrace_append hprefix tailTrace_2596094
  have hstable : (prefixWord ++ tailWord_2596094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596094).length < 2 ^ (prefixWord ++ tailWord_2596094).sum := by decide
  have hdescent : baseEnd_2596094 < baseStart_2596094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596193 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2596193 : Nat := 118140960795 + 2596193 * 2 ^ 59
def prefixEnd_2596193 : Nat := 4983230072969 + 3 ^ 40 * 2596193 * 2
def baseEnd_2596193 : Nat := 888729920558844077765221

theorem tailTrace_2596193 : CollatzResearch.WordTrace tailWord_2596193 prefixEnd_2596193 888729920558844077765221 := by
  unfold tailWord_2596193
  simp only [CollatzResearch.WordTrace]
  refine ⟨94690937883443630309073233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63127291922295753539382155 94690937883443630309073233)
  ·
    refine ⟨71018203412582722731804925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94690937883443630309073233 71018203412582722731804925)
    ·
      refine ⟨26631826279718521024426847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71018203412582722731804925 26631826279718521024426847)
      ·
        refine ⟨39947739419577781536640271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26631826279718521024426847 39947739419577781536640271)
        ·
          refine ⟨59921609129366672304960407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39947739419577781536640271 59921609129366672304960407)
          ·
            refine ⟨89882413694050008457440611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59921609129366672304960407 89882413694050008457440611)
            ·
              refine ⟨134823620541075012686160917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89882413694050008457440611 134823620541075012686160917)
              ·
                refine ⟨6319857212862891219663793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134823620541075012686160917 6319857212862891219663793)
                ·
                  refine ⟨4739892909647168414747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6319857212862891219663793 4739892909647168414747845)
                  ·
                    refine ⟨888729920558844077765221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739892909647168414747845 888729920558844077765221)
                    ·
                      rfl

theorem cell22_2596193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2596193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596193 prefixEnd_2596193 := by exact prefixLift 2596193
  have htrace : WordTrace (prefixWord ++ tailWord_2596193) baseStart_2596193 baseEnd_2596193 := by
    simpa [prefixWord, tailWord_2596193, baseEnd_2596193] using wordTrace_append hprefix tailTrace_2596193
  have hstable : (prefixWord ++ tailWord_2596193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596193).length < 2 ^ (prefixWord ++ tailWord_2596193).sum := by decide
  have hdescent : baseEnd_2596193 < baseStart_2596193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596195 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 4, 3]
def baseStart_2596195 : Nat := 118140960795 + 2596195 * 2 ^ 59
def prefixEnd_2596195 : Nat := 4983230072969 + 3 ^ 40 * 2596195 * 2
def baseEnd_2596195 : Nat := 888730605199716739215215

theorem tailTrace_2596195 : CollatzResearch.WordTrace tailWord_2596195 prefixEnd_2596195 888730605199716739215215 := by
  unfold tailWord_2596195
  simp only [CollatzResearch.WordTrace]
  refine ⟨94691010829436384650646039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63127340552957589767097359 94691010829436384650646039)
  ·
    refine ⟨142036516244154576975969059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94691010829436384650646039 142036516244154576975969059)
    ·
      refine ⟨213054774366231865463953589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142036516244154576975969059 213054774366231865463953589)
      ·
        refine ⟨19973885096834237387245649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213054774366231865463953589 19973885096834237387245649)
        ·
          refine ⟨14980413822625678040434237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19973885096834237387245649 14980413822625678040434237)
          ·
            refine ⟨5617655183484629265162839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14980413822625678040434237 5617655183484629265162839)
            ·
              refine ⟨8426482775226943897744259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617655183484629265162839 8426482775226943897744259)
              ·
                refine ⟨12639724162840415846616389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8426482775226943897744259 12639724162840415846616389)
                ·
                  refine ⟨2369948280532577971240573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12639724162840415846616389 2369948280532577971240573)
                  ·
                    refine ⟨888730605199716739215215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369948280532577971240573 888730605199716739215215)
                    ·
                      rfl

theorem cell22_2596195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 3].length) (baseStart_2596195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596195 prefixEnd_2596195 := by exact prefixLift 2596195
  have htrace : WordTrace (prefixWord ++ tailWord_2596195) baseStart_2596195 baseEnd_2596195 := by
    simpa [prefixWord, tailWord_2596195, baseEnd_2596195] using wordTrace_append hprefix tailTrace_2596195
  have hstable : (prefixWord ++ tailWord_2596195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596195).length < 2 ^ (prefixWord ++ tailWord_2596195).sum := by decide
  have hdescent : baseEnd_2596195 < baseStart_2596195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596225 : List Nat := [1, 2, 4, 3, 2, 1, 1, 8]
def baseStart_2596225 : Nat := 118140960795 + 2596225 * 2 ^ 59
def prefixEnd_2596225 : Nat := 4983230072969 + 3 ^ 40 * 2596225 * 2
def baseEnd_2596225 : Nat := 98748986090311851218347

theorem tailTrace_2596225 : CollatzResearch.WordTrace tailWord_2596225 prefixEnd_2596225 98748986090311851218347 := by
  unfold tailWord_2596225
  simp only [CollatzResearch.WordTrace]
  refine ⟨94692105019327699774238129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63128070012885133182825419 94692105019327699774238129)
  ·
    refine ⟨71019078764495774830678597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94692105019327699774238129 71019078764495774830678597)
    ·
      refine ⟨13316077268342957780752237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71019078764495774830678597 13316077268342957780752237)
      ·
        refine ⟨4993528975628609167782089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13316077268342957780752237 4993528975628609167782089)
        ·
          refine ⟨3745146731721456875836567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4993528975628609167782089 3745146731721456875836567)
          ·
            refine ⟨5617720097582185313754851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745146731721456875836567 5617720097582185313754851)
            ·
              refine ⟨8426580146373277970632277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617720097582185313754851 8426580146373277970632277)
              ·
                refine ⟨98748986090311851218347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8426580146373277970632277 98748986090311851218347)
                ·
                  rfl

theorem cell22_2596225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 8].length) (baseStart_2596225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596225 prefixEnd_2596225 := by exact prefixLift 2596225
  have htrace : WordTrace (prefixWord ++ tailWord_2596225) baseStart_2596225 baseEnd_2596225 := by
    simpa [prefixWord, tailWord_2596225, baseEnd_2596225] using wordTrace_append hprefix tailTrace_2596225
  have hstable : (prefixWord ++ tailWord_2596225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596225).length < 2 ^ (prefixWord ++ tailWord_2596225).sum := by decide
  have hdescent : baseEnd_2596225 < baseStart_2596225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596242 : List Nat := [3, 2, 3, 3, 1, 2, 8]
def baseStart_2596242 : Nat := 118140960795 + 2596242 * 2 ^ 59
def prefixEnd_2596242 : Nat := 4983230072969 + 3 ^ 40 * 2596242 * 2
def baseEnd_2596242 : Nat := 32916544231860158640373

theorem tailTrace_2596242 : CollatzResearch.WordTrace tailWord_2596242 prefixEnd_2596242 32916544231860158640373 := by
  unfold tailWord_2596242
  simp only [CollatzResearch.WordTrace]
  refine ⟨23673181265066527919401745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63128483373510741118404653 23673181265066527919401745)
  ·
    refine ⟨17754885948799895939551309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23673181265066527919401745 17754885948799895939551309)
    ·
      refine ⟨6658082230799960977331741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17754885948799895939551309 6658082230799960977331741)
      ·
        refine ⟨2496780836549985366499403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6658082230799960977331741 2496780836549985366499403)
        ·
          refine ⟨3745171254824978049749105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496780836549985366499403 3745171254824978049749105)
          ·
            refine ⟨2808878441118733537311829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3745171254824978049749105 2808878441118733537311829)
            ·
              refine ⟨32916544231860158640373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2808878441118733537311829 32916544231860158640373)
              ·
                rfl

theorem cell22_2596242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 8].length) (baseStart_2596242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596242 prefixEnd_2596242 := by exact prefixLift 2596242
  have htrace : WordTrace (prefixWord ++ tailWord_2596242) baseStart_2596242 baseEnd_2596242 := by
    simpa [prefixWord, tailWord_2596242, baseEnd_2596242] using wordTrace_append hprefix tailTrace_2596242
  have hstable : (prefixWord ++ tailWord_2596242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596242).length < 2 ^ (prefixWord ++ tailWord_2596242).sum := by decide
  have hdescent : baseEnd_2596242 < baseStart_2596242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596268 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_2596268 : Nat := 118140960795 + 2596268 * 2 ^ 59
def prefixEnd_2596268 : Nat := 4983230072969 + 3 ^ 40 * 2596268 * 2
def baseEnd_2596268 : Nat := 888755594591568882139991

theorem tailTrace_2596268 : CollatzResearch.WordTrace tailWord_2596268 prefixEnd_2596268 888755594591568882139991 := by
  unfold tailWord_2596268
  simp only [CollatzResearch.WordTrace]
  refine ⟨47346836679085959059026729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63129115572114612078702305 47346836679085959059026729)
  ·
    refine ⟨35510127509314469294270047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47346836679085959059026729 35510127509314469294270047)
    ·
      refine ⟨53265191263971703941405071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35510127509314469294270047 53265191263971703941405071)
      ·
        refine ⟨79897786895957555912107607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53265191263971703941405071 79897786895957555912107607)
        ·
          refine ⟨119846680343936333868161411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79897786895957555912107607 119846680343936333868161411)
          ·
            refine ⟨179770020515904500802242117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119846680343936333868161411 179770020515904500802242117)
            ·
              refine ⟨33706878846732093900420397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179770020515904500802242117 33706878846732093900420397)
              ·
                refine ⟨12640079567524535212657649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33706878846732093900420397 12640079567524535212657649)
                ·
                  refine ⟨9480059675643401409493237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12640079567524535212657649 9480059675643401409493237)
                  ·
                    refine ⟨888755594591568882139991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9480059675643401409493237 888755594591568882139991)
                    ·
                      rfl

theorem cell22_2596268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_2596268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596268 prefixEnd_2596268 := by exact prefixLift 2596268
  have htrace : WordTrace (prefixWord ++ tailWord_2596268) baseStart_2596268 baseEnd_2596268 := by
    simpa [prefixWord, tailWord_2596268, baseEnd_2596268] using wordTrace_append hprefix tailTrace_2596268
  have hstable : (prefixWord ++ tailWord_2596268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596268).length < 2 ^ (prefixWord ++ tailWord_2596268).sum := by decide
  have hdescent : baseEnd_2596268 < baseStart_2596268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596308 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2596308 : Nat := 118140960795 + 2596308 * 2 ^ 59
def prefixEnd_2596308 : Nat := 4983230072969 + 3 ^ 40 * 2596308 * 2
def baseEnd_2596308 : Nat := 888769287409022111139869

theorem tailTrace_2596308 : CollatzResearch.WordTrace tailWord_2596308 prefixEnd_2596308 888769287409022111139869 := by
  unfold tailWord_2596308
  simp only [CollatzResearch.WordTrace]
  refine ⟨47347566139013502474754789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63130088185351336633006385 47347566139013502474754789)
  ·
    refine ⟨8877668651065031714016523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47347566139013502474754789 8877668651065031714016523)
    ·
      refine ⟨13316502976597547571024785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8877668651065031714016523 13316502976597547571024785)
      ·
        refine ⟨9987377232448160678268589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13316502976597547571024785 9987377232448160678268589)
        ·
          refine ⟨3745266462168060254350721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9987377232448160678268589 3745266462168060254350721)
          ·
            refine ⟨2808949846626045190763041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3745266462168060254350721 2808949846626045190763041)
            ·
              refine ⟨2106712384969533893072281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808949846626045190763041 2106712384969533893072281)
              ·
                refine ⟨1580034288727150419804211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106712384969533893072281 1580034288727150419804211)
                ·
                  refine ⟨2370051433090725629706317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580034288727150419804211 2370051433090725629706317)
                  ·
                    refine ⟨888769287409022111139869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370051433090725629706317 888769287409022111139869)
                    ·
                      rfl

theorem cell22_2596308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2596308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596308 prefixEnd_2596308 := by exact prefixLift 2596308
  have htrace : WordTrace (prefixWord ++ tailWord_2596308) baseStart_2596308 baseEnd_2596308 := by
    simpa [prefixWord, tailWord_2596308, baseEnd_2596308] using wordTrace_append hprefix tailTrace_2596308
  have hstable : (prefixWord ++ tailWord_2596308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596308).length < 2 ^ (prefixWord ++ tailWord_2596308).sum := by decide
  have hdescent : baseEnd_2596308 < baseStart_2596308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596405 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 7]
def baseStart_2596405 : Nat := 118140960795 + 2596405 * 2 ^ 59
def prefixEnd_2596405 : Nat := 4983230072969 + 3 ^ 40 * 2596405 * 2
def baseEnd_2596405 : Nat := 296267497497115397154857

theorem tailTrace_2596405 : CollatzResearch.WordTrace tailWord_2596405 prefixEnd_2596405 296267497497115397154857 := by
  unfold tailWord_2596405
  simp only [CollatzResearch.WordTrace]
  refine ⟨94698670158675590515790669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63132446772450393677193779 94698670158675590515790669)
  ·
    refine ⟨35512001309503346443421501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94698670158675590515790669 35512001309503346443421501)
    ·
      refine ⟨13317000491063754916283063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35512001309503346443421501 13317000491063754916283063)
      ·
        refine ⟨19975500736595632374424595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13317000491063754916283063 19975500736595632374424595)
        ·
          refine ⟨29963251104893448561636893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19975500736595632374424595 29963251104893448561636893)
          ·
            refine ⟨11236219164335043210613835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29963251104893448561636893 11236219164335043210613835)
            ·
              refine ⟨16854328746502564815920753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11236219164335043210613835 16854328746502564815920753)
              ·
                refine ⟨12640746559876923611940565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16854328746502564815920753 12640746559876923611940565)
                ·
                  refine ⟨296267497497115397154857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12640746559876923611940565 296267497497115397154857)
                  ·
                    rfl

theorem cell22_2596405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_2596405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596405 prefixEnd_2596405 := by exact prefixLift 2596405
  have htrace : WordTrace (prefixWord ++ tailWord_2596405) baseStart_2596405 baseEnd_2596405 := by
    simpa [prefixWord, tailWord_2596405, baseEnd_2596405] using wordTrace_append hprefix tailTrace_2596405
  have hstable : (prefixWord ++ tailWord_2596405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596405).length < 2 ^ (prefixWord ++ tailWord_2596405).sum := by decide
  have hdescent : baseEnd_2596405 < baseStart_2596405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596426 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_2596426 : Nat := 118140960795 + 2596426 * 2 ^ 59
def prefixEnd_2596426 : Nat := 4983230072969 + 3 ^ 40 * 2596426 * 2
def baseEnd_2596426 : Nat := 888809681220509136689507

theorem tailTrace_2596426 : CollatzResearch.WordTrace tailWord_2596426 prefixEnd_2596426 888809681220509136689507 := by
  unfold tailWord_2596426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23674859022899877775576283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63132957394399674068203421 23674859022899877775576283)
  ·
    refine ⟨35512288534349816663364425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23674859022899877775576283 35512288534349816663364425)
    ·
      refine ⟨26634216400762362497523319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35512288534349816663364425 26634216400762362497523319)
      ·
        refine ⟨39951324601143543746284979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26634216400762362497523319 39951324601143543746284979)
        ·
          refine ⟨59926986901715315619427469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39951324601143543746284979 59926986901715315619427469)
          ·
            refine ⟨22472620088143243357285301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59926986901715315619427469 22472620088143243357285301)
            ·
              refine ⟨2106808133263429064745497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22472620088143243357285301 2106808133263429064745497)
              ·
                refine ⟨1580106099947571798559123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106808133263429064745497 1580106099947571798559123)
                ·
                  refine ⟨2370159149921357697838685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580106099947571798559123 2370159149921357697838685)
                  ·
                    refine ⟨888809681220509136689507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370159149921357697838685 888809681220509136689507)
                    ·
                      rfl

theorem cell22_2596426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_2596426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596426 prefixEnd_2596426 := by exact prefixLift 2596426
  have htrace : WordTrace (prefixWord ++ tailWord_2596426) baseStart_2596426 baseEnd_2596426 := by
    simpa [prefixWord, tailWord_2596426, baseEnd_2596426] using wordTrace_append hprefix tailTrace_2596426
  have hstable : (prefixWord ++ tailWord_2596426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596426).length < 2 ^ (prefixWord ++ tailWord_2596426).sum := by decide
  have hdescent : baseEnd_2596426 < baseStart_2596426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596439 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 5]
def baseStart_2596439 : Nat := 118140960795 + 2596439 * 2 ^ 59
def prefixEnd_2596439 : Nat := 4983230072969 + 3 ^ 40 * 2596439 * 2
def baseEnd_2596439 : Nat := 296271377128727145371489

theorem tailTrace_2596439 : CollatzResearch.WordTrace tailWord_2596439 prefixEnd_2596439 296271377128727145371489 := by
  unfold tailWord_2596439
  simp only [CollatzResearch.WordTrace]
  refine ⟨94699910240552414322528371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63133273493701609548352247 94699910240552414322528371)
  ·
    refine ⟨142049865360828621483792557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94699910240552414322528371 142049865360828621483792557)
    ·
      refine ⟨53268699510310733056422209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142049865360828621483792557 53268699510310733056422209)
      ·
        refine ⟨39951524632733049792316657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53268699510310733056422209 39951524632733049792316657)
        ·
          refine ⟨29963643474549787344237493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39951524632733049792316657 29963643474549787344237493)
          ·
            refine ⟨2809091575739042563522265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29963643474549787344237493 2809091575739042563522265)
            ·
              refine ⟨2106818681804281922641699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2809091575739042563522265 2106818681804281922641699)
              ·
                refine ⟨3160228022706422883962549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106818681804281922641699 3160228022706422883962549)
                ·
                  refine ⟨296271377128727145371489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3160228022706422883962549 296271377128727145371489)
                  ·
                    rfl

theorem cell22_2596439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 5].length) (baseStart_2596439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596439 prefixEnd_2596439 := by exact prefixLift 2596439
  have htrace : WordTrace (prefixWord ++ tailWord_2596439) baseStart_2596439 baseEnd_2596439 := by
    simpa [prefixWord, tailWord_2596439, baseEnd_2596439] using wordTrace_append hprefix tailTrace_2596439
  have hstable : (prefixWord ++ tailWord_2596439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596439).length < 2 ^ (prefixWord ++ tailWord_2596439).sum := by decide
  have hdescent : baseEnd_2596439 < baseStart_2596439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596452 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2596452 : Nat := 118140960795 + 2596452 * 2 ^ 59
def prefixEnd_2596452 : Nat := 4983230072969 + 3 ^ 40 * 2596452 * 2
def baseEnd_2596452 : Nat := 888818581551853735539427

theorem tailTrace_2596452 : CollatzResearch.WordTrace tailWord_2596452 prefixEnd_2596452 888818581551853735539427 := by
  unfold tailWord_2596452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47350192194752658771375805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63133589593003545028501073 47350192194752658771375805)
  ·
    refine ⟨17756322073032247039265927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47350192194752658771375805 17756322073032247039265927)
    ·
      refine ⟨26634483109548370558898891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17756322073032247039265927 26634483109548370558898891)
      ·
        refine ⟨39951724664322555838348337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26634483109548370558898891 39951724664322555838348337)
        ·
          refine ⟨29963793498241916878761253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39951724664322555838348337 29963793498241916878761253)
          ·
            refine ⟨5618211280920359414767735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29963793498241916878761253 5618211280920359414767735)
            ·
              refine ⟨8427316921380539122151603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5618211280920359414767735 8427316921380539122151603)
              ·
                refine ⟨12640975382070808683227405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8427316921380539122151603 12640975382070808683227405)
                ·
                  refine ⟨4740365768276553256210277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12640975382070808683227405 4740365768276553256210277)
                  ·
                    refine ⟨888818581551853735539427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4740365768276553256210277 888818581551853735539427)
                    ·
                      rfl

theorem cell22_2596452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2596452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596452 prefixEnd_2596452 := by exact prefixLift 2596452
  have htrace : WordTrace (prefixWord ++ tailWord_2596452) baseStart_2596452 baseEnd_2596452 := by
    simpa [prefixWord, tailWord_2596452, baseEnd_2596452] using wordTrace_append hprefix tailTrace_2596452
  have hstable : (prefixWord ++ tailWord_2596452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596452).length < 2 ^ (prefixWord ++ tailWord_2596452).sum := by decide
  have hdescent : baseEnd_2596452 < baseStart_2596452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596527 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 5, 3]
def baseStart_2596527 : Nat := 118140960795 + 2596527 * 2 ^ 59
def prefixEnd_2596527 : Nat := 4983230072969 + 3 ^ 40 * 2596527 * 2
def baseEnd_2596527 : Nat := 888844255584578539914197

theorem tailTrace_2596527 : CollatzResearch.WordTrace tailWord_2596527 prefixEnd_2596527 888844255584578539914197 := by
  unfold tailWord_2596527
  simp only [CollatzResearch.WordTrace]
  refine ⟨94703119864233605351731835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63135413242822403567821223 94703119864233605351731835)
  ·
    refine ⟨142054679796350408027597753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94703119864233605351731835 142054679796350408027597753)
    ·
      refine ⟨106541009847262806020698315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142054679796350408027597753 106541009847262806020698315)
      ·
        refine ⟨159811514770894209031047473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106541009847262806020698315 159811514770894209031047473)
        ·
          refine ⟨119858636078170656773285605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159811514770894209031047473 119858636078170656773285605)
          ·
            refine ⟨22473494264656998144991051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119858636078170656773285605 22473494264656998144991051)
            ·
              refine ⟨33710241396985497217486577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22473494264656998144991051 33710241396985497217486577)
              ·
                refine ⟨25282681047739122913114933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33710241396985497217486577 25282681047739122913114933)
                ·
                  refine ⟨2370251348225542773104525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25282681047739122913114933 2370251348225542773104525)
                  ·
                    refine ⟨888844255584578539914197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370251348225542773104525 888844255584578539914197)
                    ·
                      rfl

theorem cell22_2596527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_2596527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596527 prefixEnd_2596527 := by exact prefixLift 2596527
  have htrace : WordTrace (prefixWord ++ tailWord_2596527) baseStart_2596527 baseEnd_2596527 := by
    simpa [prefixWord, tailWord_2596527, baseEnd_2596527] using wordTrace_append hprefix tailTrace_2596527
  have hstable : (prefixWord ++ tailWord_2596527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596527).length < 2 ^ (prefixWord ++ tailWord_2596527).sum := by decide
  have hdescent : baseEnd_2596527 < baseStart_2596527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596533 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2596533 : Nat := 118140960795 + 2596533 * 2 ^ 59
def prefixEnd_2596533 : Nat := 4983230072969 + 3 ^ 40 * 2596533 * 2
def baseEnd_2596533 : Nat := 888846309507196524264179

theorem tailTrace_2596533 : CollatzResearch.WordTrace tailWord_2596533 prefixEnd_2596533 888846309507196524264179 := by
  unfold tailWord_2596533
  simp only [CollatzResearch.WordTrace]
  refine ⟨94703338702211868376450253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63135559134807912250966835 94703338702211868376450253)
  ·
    refine ⟨35513752013329450641168845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94703338702211868376450253 35513752013329450641168845)
    ·
      refine ⟨13317657004998543990438317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35513752013329450641168845 13317657004998543990438317)
      ·
        refine ⟨4994121376874453996414369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13317657004998543990438317 4994121376874453996414369)
        ·
          refine ⟨3745591032655840497310777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4994121376874453996414369 3745591032655840497310777)
          ·
            refine ⟨2809193274491880372983083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3745591032655840497310777 2809193274491880372983083)
            ·
              refine ⟨4213789911737820559474625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809193274491880372983083 4213789911737820559474625)
              ·
                refine ⟨3160342433803365419605969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4213789911737820559474625 3160342433803365419605969)
                ·
                  refine ⟨2370256825352524064704477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3160342433803365419605969 2370256825352524064704477)
                  ·
                    refine ⟨888846309507196524264179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370256825352524064704477 888846309507196524264179)
                    ·
                      rfl

theorem cell22_2596533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2596533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596533 prefixEnd_2596533 := by exact prefixLift 2596533
  have htrace : WordTrace (prefixWord ++ tailWord_2596533) baseStart_2596533 baseEnd_2596533 := by
    simpa [prefixWord, tailWord_2596533, baseEnd_2596533] using wordTrace_append hprefix tailTrace_2596533
  have hstable : (prefixWord ++ tailWord_2596533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596533).length < 2 ^ (prefixWord ++ tailWord_2596533).sum := by decide
  have hdescent : baseEnd_2596533 < baseStart_2596533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596544 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_2596544 : Nat := 118140960795 + 2596544 * 2 ^ 59
def prefixEnd_2596544 : Nat := 4983230072969 + 3 ^ 40 * 2596544 * 2
def baseEnd_2596544 : Nat := 888850075031996162239145

theorem tailTrace_2596544 : CollatzResearch.WordTrace tailWord_2596544 prefixEnd_2596544 888850075031996162239145 := by
  unfold tailWord_2596544
  simp only [CollatzResearch.WordTrace]
  refine ⟨47351869952586008627550343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63135826603448011503400457 47351869952586008627550343)
  ·
    refine ⟨71027804928879012941325515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47351869952586008627550343 71027804928879012941325515)
    ·
      refine ⟨106541707393318519411988273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71027804928879012941325515 106541707393318519411988273)
      ·
        refine ⟨79906280544988889558991205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106541707393318519411988273 79906280544988889558991205)
        ·
          refine ⟨14982427602185416792310851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79906280544988889558991205 14982427602185416792310851)
          ·
            refine ⟨22473641403278125188466277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14982427602185416792310851 22473641403278125188466277)
            ·
              refine ⟨4213807763114648472837427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22473641403278125188466277 4213807763114648472837427)
              ·
                refine ⟨6320711644671972709256141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4213807763114648472837427 6320711644671972709256141)
                ·
                  refine ⟨2370266866751989765971053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6320711644671972709256141 2370266866751989765971053)
                  ·
                    refine ⟨888850075031996162239145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370266866751989765971053 888850075031996162239145)
                    ·
                      rfl

theorem cell22_2596544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_2596544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596544 prefixEnd_2596544 := by exact prefixLift 2596544
  have htrace : WordTrace (prefixWord ++ tailWord_2596544) baseStart_2596544 baseEnd_2596544 := by
    simpa [prefixWord, tailWord_2596544, baseEnd_2596544] using wordTrace_append hprefix tailTrace_2596544
  have hstable : (prefixWord ++ tailWord_2596544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596544).length < 2 ^ (prefixWord ++ tailWord_2596544).sum := by decide
  have hdescent : baseEnd_2596544 < baseStart_2596544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596617 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_2596617 : Nat := 118140960795 + 2596617 * 2 ^ 59
def prefixEnd_2596617 : Nat := 4983230072969 + 3 ^ 40 * 2596617 * 2
def baseEnd_2596617 : Nat := 888875064423848305163921

theorem tailTrace_2596617 : CollatzResearch.WordTrace tailWord_2596617 prefixEnd_2596617 888875064423848305163921 := by
  unfold tailWord_2596617
  simp only [CollatzResearch.WordTrace]
  refine ⟨94706402433907550722508105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63137601622605033815005403 94706402433907550722508105)
  ·
    refine ⟨71029801825430663041881079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94706402433907550722508105 71029801825430663041881079)
    ·
      refine ⟨106544702738145994562821619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71029801825430663041881079 106544702738145994562821619)
      ·
        refine ⟨159817054107218991844232429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106544702738145994562821619 159817054107218991844232429)
        ·
          refine ⟨59931395290207121941587161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159817054107218991844232429 59931395290207121941587161)
          ·
            refine ⟨44948546467655341456190371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59931395290207121941587161 44948546467655341456190371)
            ·
              refine ⟨67422819701483012184285557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44948546467655341456190371 67422819701483012184285557)
              ·
                refine ⟨6320889347014032392276771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67422819701483012184285557 6320889347014032392276771)
                ·
                  refine ⟨9481334020521048588415157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6320889347014032392276771 9481334020521048588415157)
                  ·
                    refine ⟨888875064423848305163921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9481334020521048588415157 888875064423848305163921)
                    ·
                      rfl

theorem cell22_2596617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_2596617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596617 prefixEnd_2596617 := by exact prefixLift 2596617
  have htrace : WordTrace (prefixWord ++ tailWord_2596617) baseStart_2596617 baseEnd_2596617 := by
    simpa [prefixWord, tailWord_2596617, baseEnd_2596617] using wordTrace_append hprefix tailTrace_2596617
  have hstable : (prefixWord ++ tailWord_2596617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596617).length < 2 ^ (prefixWord ++ tailWord_2596617).sum := by decide
  have hdescent : baseEnd_2596617 < baseStart_2596617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596632 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_2596632 : Nat := 118140960795 + 2596632 * 2 ^ 59
def prefixEnd_2596632 : Nat := 4983230072969 + 3 ^ 40 * 2596632 * 2
def baseEnd_2596632 : Nat := 888880199230393266038875

theorem tailTrace_2596632 : CollatzResearch.WordTrace tailWord_2596632 prefixEnd_2596632 888880199230393266038875 := by
  unfold tailWord_2596632
  simp only [CollatzResearch.WordTrace]
  refine ⟨47353474764426604142152075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63137966352568805522869433 47353474764426604142152075)
  ·
    refine ⟨71030212146639906213228113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47353474764426604142152075 71030212146639906213228113)
    ·
      refine ⟨53272659109979929659921085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71030212146639906213228113 53272659109979929659921085)
      ·
        refine ⟨19977247166242473622470407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53272659109979929659921085 19977247166242473622470407)
        ·
          refine ⟨29965870749363710433705611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19977247166242473622470407 29965870749363710433705611)
          ·
            refine ⟨44948806124045565650558417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29965870749363710433705611 44948806124045565650558417)
            ·
              refine ⟨33711604593034174237918813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44948806124045565650558417 33711604593034174237918813)
              ·
                refine ⟨12641851722387815339219555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33711604593034174237918813 12641851722387815339219555)
                ·
                  refine ⟨18962777583581723008829333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12641851722387815339219555 18962777583581723008829333)
                  ·
                    refine ⟨888880199230393266038875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18962777583581723008829333 888880199230393266038875)
                    ·
                      rfl

theorem cell22_2596632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_2596632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596632 prefixEnd_2596632 := by exact prefixLift 2596632
  have htrace : WordTrace (prefixWord ++ tailWord_2596632) baseStart_2596632 baseEnd_2596632 := by
    simpa [prefixWord, tailWord_2596632, baseEnd_2596632] using wordTrace_append hprefix tailTrace_2596632
  have hstable : (prefixWord ++ tailWord_2596632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596632).length < 2 ^ (prefixWord ++ tailWord_2596632).sum := by decide
  have hdescent : baseEnd_2596632 < baseStart_2596632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596634 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_2596634 : Nat := 118140960795 + 2596634 * 2 ^ 59
def prefixEnd_2596634 : Nat := 4983230072969 + 3 ^ 40 * 2596634 * 2
def baseEnd_2596634 : Nat := 888880883871265927488869

theorem tailTrace_2596634 : CollatzResearch.WordTrace tailWord_2596634 prefixEnd_2596634 888880883871265927488869 := by
  unfold tailWord_2596634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23676755618711490656469239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63138014983230641750584637 23676755618711490656469239)
  ·
    refine ⟨35515133428067235984703859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23676755618711490656469239 35515133428067235984703859)
    ·
      refine ⟨53272700142100853977055789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35515133428067235984703859 53272700142100853977055789)
      ·
        refine ⟨19977262553287820241395921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53272700142100853977055789 19977262553287820241395921)
        ·
          refine ⟨14982946914965865181046941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19977262553287820241395921 14982946914965865181046941)
          ·
            refine ⟨5618605093112199442892603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14982946914965865181046941 5618605093112199442892603)
            ·
              refine ⟨8427907639668299164338905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5618605093112199442892603 8427907639668299164338905)
              ·
                refine ⟨6320930729751224373254179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8427907639668299164338905 6320930729751224373254179)
                ·
                  refine ⟨9481396094626836559881269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6320930729751224373254179 9481396094626836559881269)
                  ·
                    refine ⟨888880883871265927488869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9481396094626836559881269 888880883871265927488869)
                    ·
                      rfl

theorem cell22_2596634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_2596634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596634 prefixEnd_2596634 := by exact prefixLift 2596634
  have htrace : WordTrace (prefixWord ++ tailWord_2596634) baseStart_2596634 baseEnd_2596634 := by
    simpa [prefixWord, tailWord_2596634, baseEnd_2596634] using wordTrace_append hprefix tailTrace_2596634
  have hstable : (prefixWord ++ tailWord_2596634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596634).length < 2 ^ (prefixWord ++ tailWord_2596634).sum := by decide
  have hdescent : baseEnd_2596634 < baseStart_2596634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596664 : List Nat := [2, 1, 2, 1, 3, 5, 1, 7]
def baseStart_2596664 : Nat := 118140960795 + 2596664 * 2 ^ 59
def prefixEnd_2596664 : Nat := 4983230072969 + 3 ^ 40 * 2596664 * 2
def baseEnd_2596664 : Nat := 98765683720483983248753

theorem tailTrace_2596664 : CollatzResearch.WordTrace tailWord_2596664 prefixEnd_2596664 98765683720483983248753 := by
  unfold tailWord_2596664
  simp only [CollatzResearch.WordTrace]
  refine ⟨47354058332368638874734523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63138744443158185166312697 47354058332368638874734523)
  ·
    refine ⟨71031087498552958312101785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47354058332368638874734523 71031087498552958312101785)
    ·
      refine ⟨53273315623914718734076339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71031087498552958312101785 53273315623914718734076339)
      ·
        refine ⟨79909973435872078101114509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53273315623914718734076339 79909973435872078101114509)
        ·
          refine ⟨29966240038452029287917941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79909973435872078101114509 29966240038452029287917941)
          ·
            refine ⟨2809335003604877745742307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29966240038452029287917941 2809335003604877745742307)
            ·
              refine ⟨4214002505407316618613461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809335003604877745742307 4214002505407316618613461)
              ·
                refine ⟨98765683720483983248753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4214002505407316618613461 98765683720483983248753)
                ·
                  rfl

theorem cell22_2596664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_2596664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596664 prefixEnd_2596664 := by exact prefixLift 2596664
  have htrace : WordTrace (prefixWord ++ tailWord_2596664) baseStart_2596664 baseEnd_2596664 := by
    simpa [prefixWord, tailWord_2596664, baseEnd_2596664] using wordTrace_append hprefix tailTrace_2596664
  have hstable : (prefixWord ++ tailWord_2596664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596664).length < 2 ^ (prefixWord ++ tailWord_2596664).sum := by decide
  have hdescent : baseEnd_2596664 < baseStart_2596664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596677 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2596677 : Nat := 118140960795 + 2596677 * 2 ^ 59
def prefixEnd_2596677 : Nat := 4983230072969 + 3 ^ 40 * 2596677 * 2
def baseEnd_2596677 : Nat := 888895603650028148663737

theorem tailTrace_2596677 : CollatzResearch.WordTrace tailWord_2596677 prefixEnd_2596677 888895603650028148663737 := by
  unfold tailWord_2596677
  simp only [CollatzResearch.WordTrace]
  refine ⟨94708590813690180969692285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63139060542460120646461523 94708590813690180969692285)
  ·
    refine ⟨35515721555133817863634607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94708590813690180969692285 35515721555133817863634607)
    ·
      refine ⟨53273582332700726795451911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35515721555133817863634607 53273582332700726795451911)
      ·
        refine ⟨79910373499051090193177867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53273582332700726795451911 79910373499051090193177867)
        ·
          refine ⟨119865560248576635289766801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79910373499051090193177867 119865560248576635289766801)
          ·
            refine ⟨89899170186432476467325101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119865560248576635289766801 89899170186432476467325101)
            ·
              refine ⟨33712188819912178675246913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89899170186432476467325101 33712188819912178675246913)
              ·
                refine ⟨25284141614934134006435185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33712188819912178675246913 25284141614934134006435185)
                ·
                  refine ⟨18963106211200600504826389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25284141614934134006435185 18963106211200600504826389)
                  ·
                    refine ⟨888895603650028148663737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18963106211200600504826389 888895603650028148663737)
                    ·
                      rfl

theorem cell22_2596677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2596677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596677 prefixEnd_2596677 := by exact prefixLift 2596677
  have htrace : WordTrace (prefixWord ++ tailWord_2596677) baseStart_2596677 baseEnd_2596677 := by
    simpa [prefixWord, tailWord_2596677, baseEnd_2596677] using wordTrace_append hprefix tailTrace_2596677
  have hstable : (prefixWord ++ tailWord_2596677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596677).length < 2 ^ (prefixWord ++ tailWord_2596677).sum := by decide
  have hdescent : baseEnd_2596677 < baseStart_2596677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596679 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 5, 3]
def baseStart_2596679 : Nat := 118140960795 + 2596679 * 2 ^ 59
def prefixEnd_2596679 : Nat := 4983230072969 + 3 ^ 40 * 2596679 * 2
def baseEnd_2596679 : Nat := 888896288290900810113731

theorem tailTrace_2596679 : CollatzResearch.WordTrace tailWord_2596679 prefixEnd_2596679 888896288290900810113731 := by
  unfold tailWord_2596679
  simp only [CollatzResearch.WordTrace]
  refine ⟨94708663759682935311265091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63139109173121956874176727 94708663759682935311265091)
  ·
    refine ⟨142062995639524402966897637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94708663759682935311265091 142062995639524402966897637)
    ·
      refine ⟨26636811682410825556293307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142062995639524402966897637 26636811682410825556293307)
      ·
        refine ⟨39955217523616238334439961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26636811682410825556293307 39955217523616238334439961)
        ·
          refine ⟨29966413142712178750829971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39955217523616238334439961 29966413142712178750829971)
          ·
            refine ⟨44949619714068268126244957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29966413142712178750829971 44949619714068268126244957)
            ·
              refine ⟨16856107392775600547341859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44949619714068268126244957 16856107392775600547341859)
              ·
                refine ⟨25284161089163400821012789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16856107392775600547341859 25284161089163400821012789)
                ·
                  refine ⟨2370390102109068826969949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25284161089163400821012789 2370390102109068826969949)
                  ·
                    refine ⟨888896288290900810113731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370390102109068826969949 888896288290900810113731)
                    ·
                      rfl

theorem cell22_2596679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_2596679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596679 prefixEnd_2596679 := by exact prefixLift 2596679
  have htrace : WordTrace (prefixWord ++ tailWord_2596679) baseStart_2596679 baseEnd_2596679 := by
    simpa [prefixWord, tailWord_2596679, baseEnd_2596679] using wordTrace_append hprefix tailTrace_2596679
  have hstable : (prefixWord ++ tailWord_2596679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596679).length < 2 ^ (prefixWord ++ tailWord_2596679).sum := by decide
  have hdescent : baseEnd_2596679 < baseStart_2596679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596865 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2596865 : Nat := 118140960795 + 2596865 * 2 ^ 59
def prefixEnd_2596865 : Nat := 4983230072969 + 3 ^ 40 * 2596865 * 2
def baseEnd_2596865 : Nat := 888959959892058324963161

theorem tailTrace_2596865 : CollatzResearch.WordTrace tailWord_2596865 prefixEnd_2596865 888959959892058324963161 := by
  unfold tailWord_2596865
  simp only [CollatzResearch.WordTrace]
  refine ⟨94715447737009089077536049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63143631824672726051690699 94715447737009089077536049)
  ·
    refine ⟨71036585802756816808152037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94715447737009089077536049 71036585802756816808152037)
    ·
      refine ⟨13319359838016903151528507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71036585802756816808152037 13319359838016903151528507)
      ·
        refine ⟨19979039757025354727292761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13319359838016903151528507 19979039757025354727292761)
        ·
          refine ⟨14984279817769016045469571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19979039757025354727292761 14984279817769016045469571)
          ·
            refine ⟨22476419726653524068204357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14984279817769016045469571 22476419726653524068204357)
            ·
              refine ⟨4214328698747535762788317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22476419726653524068204357 4214328698747535762788317)
              ·
                refine ⟨1580373262030325911045619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4214328698747535762788317 1580373262030325911045619)
                ·
                  refine ⟨2370559893045488866568429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580373262030325911045619 2370559893045488866568429)
                  ·
                    refine ⟨888959959892058324963161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370559893045488866568429 888959959892058324963161)
                    ·
                      rfl

theorem cell22_2596865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2596865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596865 prefixEnd_2596865 := by exact prefixLift 2596865
  have htrace : WordTrace (prefixWord ++ tailWord_2596865) baseStart_2596865 baseEnd_2596865 := by
    simpa [prefixWord, tailWord_2596865, baseEnd_2596865] using wordTrace_append hprefix tailTrace_2596865
  have hstable : (prefixWord ++ tailWord_2596865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596865).length < 2 ^ (prefixWord ++ tailWord_2596865).sum := by decide
  have hdescent : baseEnd_2596865 < baseStart_2596865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596916 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_2596916 : Nat := 118140960795 + 2596916 * 2 ^ 59
def prefixEnd_2596916 : Nat := 4983230072969 + 3 ^ 40 * 2596916 * 2
def baseEnd_2596916 : Nat := 888977418234311191938005

theorem tailTrace_2596916 : CollatzResearch.WordTrace tailWord_2596916 prefixEnd_2596916 888977418234311191938005 := by
  unfold tailWord_2596916
  simp only [CollatzResearch.WordTrace]
  refine ⟨47358653929912162393821301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63144871906549549858428401 47358653929912162393821301)
  ·
    refine ⟨4439873805929265224420747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47358653929912162393821301 4439873805929265224420747)
    ·
      refine ⟨6659810708893897836631121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4439873805929265224420747 6659810708893897836631121)
      ·
        refine ⟨4994858031670423377473341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6659810708893897836631121 4994858031670423377473341)
        ·
          refine ⟨1873071761876408766552503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4994858031670423377473341 1873071761876408766552503)
          ·
            refine ⟨2809607642814613149828755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873071761876408766552503 2809607642814613149828755)
            ·
              refine ⟨4214411464221919724743133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809607642814613149828755 4214411464221919724743133)
              ·
                refine ⟨1580404299083219896778675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4214411464221919724743133 1580404299083219896778675)
                ·
                  refine ⟨2370606448624829845168013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580404299083219896778675 2370606448624829845168013)
                  ·
                    refine ⟨888977418234311191938005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370606448624829845168013 888977418234311191938005)
                    ·
                      rfl

theorem cell22_2596916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_2596916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596916 prefixEnd_2596916 := by exact prefixLift 2596916
  have htrace : WordTrace (prefixWord ++ tailWord_2596916) baseStart_2596916 baseEnd_2596916 := by
    simpa [prefixWord, tailWord_2596916, baseEnd_2596916] using wordTrace_append hprefix tailTrace_2596916
  have hstable : (prefixWord ++ tailWord_2596916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596916).length < 2 ^ (prefixWord ++ tailWord_2596916).sum := by decide
  have hdescent : baseEnd_2596916 < baseStart_2596916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596938 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2596938 : Nat := 118140960795 + 2596938 * 2 ^ 59
def prefixEnd_2596938 : Nat := 4983230072969 + 3 ^ 40 * 2596938 * 2
def baseEnd_2596938 : Nat := 888984949283910467887937

theorem tailTrace_2596938 : CollatzResearch.WordTrace tailWord_2596938 prefixEnd_2596938 888984949283910467887937 := by
  unfold tailWord_2596938
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679527566436155636235867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63145406843829748363295645 23679527566436155636235867)
  ·
    refine ⟨35519291349654233454353801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23679527566436155636235867 35519291349654233454353801)
    ·
      refine ⟨26639468512240675090765351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35519291349654233454353801 26639468512240675090765351)
      ·
        refine ⟨39959202768361012636148027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26639468512240675090765351 39959202768361012636148027)
        ·
          refine ⟨59938804152541518954222041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39959202768361012636148027 59938804152541518954222041)
          ·
            refine ⟨44954103114406139215666531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59938804152541518954222041 44954103114406139215666531)
            ·
              refine ⟨67431154671609208823499797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44954103114406139215666531 67431154671609208823499797)
              ·
                refine ⟨3160835375231681663601553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67431154671609208823499797 3160835375231681663601553)
                ·
                  refine ⟨2370626531423761247701165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3160835375231681663601553 2370626531423761247701165)
                  ·
                    refine ⟨888984949283910467887937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370626531423761247701165 888984949283910467887937)
                    ·
                      rfl

theorem cell22_2596938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2596938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596938 prefixEnd_2596938 := by exact prefixLift 2596938
  have htrace : WordTrace (prefixWord ++ tailWord_2596938) baseStart_2596938 baseEnd_2596938 := by
    simpa [prefixWord, tailWord_2596938, baseEnd_2596938] using wordTrace_append hprefix tailTrace_2596938
  have hstable : (prefixWord ++ tailWord_2596938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596938).length < 2 ^ (prefixWord ++ tailWord_2596938).sum := by decide
  have hdescent : baseEnd_2596938 < baseStart_2596938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596970 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2596970 : Nat := 118140960795 + 2596970 * 2 ^ 59
def prefixEnd_2596970 : Nat := 4983230072969 + 3 ^ 40 * 2596970 * 2
def baseEnd_2596970 : Nat := 888995903537873051087839

theorem tailTrace_2596970 : CollatzResearch.WordTrace tailWord_2596970 prefixEnd_2596970 888995903537873051087839 := by
  unfold tailWord_2596970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679819350407173002527091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63146184934419128006738909 23679819350407173002527091)
  ·
    refine ⟨35519729025610759503790637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23679819350407173002527091 35519729025610759503790637)
    ·
      refine ⟨13319898384604034813921489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35519729025610759503790637 13319898384604034813921489)
      ·
        refine ⟨9989923788453026110441117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13319898384604034813921489 9989923788453026110441117)
        ·
          refine ⟨3746221420669884791415419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9989923788453026110441117 3746221420669884791415419)
          ·
            refine ⟨5619332131004827187123129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746221420669884791415419 5619332131004827187123129)
            ·
              refine ⟨4214499098253620390342347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5619332131004827187123129 4214499098253620390342347)
              ·
                refine ⟨6321748647380430585513521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214499098253620390342347 6321748647380430585513521)
                ·
                  refine ⟨4741311485535322939135141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321748647380430585513521 4741311485535322939135141)
                  ·
                    refine ⟨888995903537873051087839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741311485535322939135141 888995903537873051087839)
                    ·
                      rfl

theorem cell22_2596970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2596970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2596970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2596970 prefixEnd_2596970 := by exact prefixLift 2596970
  have htrace : WordTrace (prefixWord ++ tailWord_2596970) baseStart_2596970 baseEnd_2596970 := by
    simpa [prefixWord, tailWord_2596970, baseEnd_2596970] using wordTrace_append hprefix tailTrace_2596970
  have hstable : (prefixWord ++ tailWord_2596970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596970).length < 2 ^ (prefixWord ++ tailWord_2596970).sum := by decide
  have hdescent : baseEnd_2596970 < baseStart_2596970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597071 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_2597071 : Nat := 118140960795 + 2597071 * 2 ^ 59
def prefixEnd_2597071 : Nat := 4983230072969 + 3 ^ 40 * 2597071 * 2
def baseEnd_2597071 : Nat := 889030477901942454312529

theorem tailTrace_2597071 : CollatzResearch.WordTrace tailWord_2597071 prefixEnd_2597071 889030477901942454312529 := by
  unfold tailWord_2597071
  simp only [CollatzResearch.WordTrace]
  refine ⟨94722961174262786259535067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63148640782841857506356711 94722961174262786259535067)
  ·
    refine ⟨142084441761394179389302601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94722961174262786259535067 142084441761394179389302601)
    ·
      refine ⟨106563331321045634541976951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142084441761394179389302601 106563331321045634541976951)
      ·
        refine ⟨159844996981568451812965427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106563331321045634541976951 159844996981568451812965427)
        ·
          refine ⟨239767495472352677719448141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159844996981568451812965427 239767495472352677719448141)
          ·
            refine ⟨89912810802132254144793053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239767495472352677719448141 89912810802132254144793053)
            ·
              refine ⟨33717304050799595304297395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89912810802132254144793053 33717304050799595304297395)
              ·
                refine ⟨50575956076199392956446093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33717304050799595304297395 50575956076199392956446093)
                ·
                  refine ⟨18965983528574772358667285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50575956076199392956446093 18965983528574772358667285)
                  ·
                    refine ⟨889030477901942454312529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18965983528574772358667285 889030477901942454312529)
                    ·
                      rfl

theorem cell22_2597071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_2597071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597071 prefixEnd_2597071 := by exact prefixLift 2597071
  have htrace : WordTrace (prefixWord ++ tailWord_2597071) baseStart_2597071 baseEnd_2597071 := by
    simpa [prefixWord, tailWord_2597071, baseEnd_2597071] using wordTrace_append hprefix tailTrace_2597071
  have hstable : (prefixWord ++ tailWord_2597071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597071).length < 2 ^ (prefixWord ++ tailWord_2597071).sum := by decide
  have hdescent : baseEnd_2597071 < baseStart_2597071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597073 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2597073 : Nat := 118140960795 + 2597073 * 2 ^ 59
def prefixEnd_2597073 : Nat := 4983230072969 + 3 ^ 40 * 2597073 * 2
def baseEnd_2597073 : Nat := 889031162542815115762523

theorem tailTrace_2597073 : CollatzResearch.WordTrace tailWord_2597073 prefixEnd_2597073 889031162542815115762523 := by
  unfold tailWord_2597073
  simp only [CollatzResearch.WordTrace]
  refine ⟨94723034120255540601107873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63148689413503693734071915 94723034120255540601107873)
  ·
    refine ⟨71042275590191655450830905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94723034120255540601107873 71042275590191655450830905)
    ·
      refine ⟨53281706692643741588123179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71042275590191655450830905 53281706692643741588123179)
      ·
        refine ⟨79922560038965612382184769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53281706692643741588123179 79922560038965612382184769)
        ·
          refine ⟨59941920029224209286638577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79922560038965612382184769 59941920029224209286638577)
          ·
            refine ⟨44956440021918156964978933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59941920029224209286638577 44956440021918156964978933)
            ·
              refine ⟨4214666252054827215466775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44956440021918156964978933 4214666252054827215466775)
              ·
                refine ⟨6321999378082240823200163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214666252054827215466775 6321999378082240823200163)
                ·
                  refine ⟨9482999067123361234800245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6321999378082240823200163 9482999067123361234800245)
                  ·
                    refine ⟨889031162542815115762523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9482999067123361234800245 889031162542815115762523)
                    ·
                      rfl

theorem cell22_2597073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2597073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597073 prefixEnd_2597073 := by exact prefixLift 2597073
  have htrace : WordTrace (prefixWord ++ tailWord_2597073) baseStart_2597073 baseEnd_2597073 := by
    simpa [prefixWord, tailWord_2597073, baseEnd_2597073] using wordTrace_append hprefix tailTrace_2597073
  have hstable : (prefixWord ++ tailWord_2597073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597073).length < 2 ^ (prefixWord ++ tailWord_2597073).sum := by decide
  have hdescent : baseEnd_2597073 < baseStart_2597073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597077 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2597077 : Nat := 118140960795 + 2597077 * 2 ^ 59
def prefixEnd_2597077 : Nat := 4983230072969 + 3 ^ 40 * 2597077 * 2
def baseEnd_2597077 : Nat := 889032531824560438662511

theorem tailTrace_2597077 : CollatzResearch.WordTrace tailWord_2597077 prefixEnd_2597077 889032531824560438662511 := by
  unfold tailWord_2597077
  simp only [CollatzResearch.WordTrace]
  refine ⟨94723180012241049284253485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63148786674827366189502323 94723180012241049284253485)
  ·
    refine ⟨35521192504590393481595057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94723180012241049284253485 35521192504590393481595057)
    ·
      refine ⟨26640894378442795111196293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35521192504590393481595057 26640894378442795111196293)
      ·
        refine ⟨4995167695958024083349305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26640894378442795111196293 4995167695958024083349305)
        ·
          refine ⟨3746375771968518062511979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4995167695958024083349305 3746375771968518062511979)
          ·
            refine ⟨5619563657952777093767969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746375771968518062511979 5619563657952777093767969)
            ·
              refine ⟨4214672743464582820325977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5619563657952777093767969 4214672743464582820325977)
              ·
                refine ⟨3161004557598437115244483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4214672743464582820325977 3161004557598437115244483)
                ·
                  refine ⟨4741506836397655672866725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161004557598437115244483 4741506836397655672866725)
                  ·
                    refine ⟨889032531824560438662511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741506836397655672866725 889032531824560438662511)
                    ·
                      rfl

theorem cell22_2597077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2597077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597077 prefixEnd_2597077 := by exact prefixLift 2597077
  have htrace : WordTrace (prefixWord ++ tailWord_2597077) baseStart_2597077 baseEnd_2597077 := by
    simpa [prefixWord, tailWord_2597077, baseEnd_2597077] using wordTrace_append hprefix tailTrace_2597077
  have hstable : (prefixWord ++ tailWord_2597077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597077).length < 2 ^ (prefixWord ++ tailWord_2597077).sum := by decide
  have hdescent : baseEnd_2597077 < baseStart_2597077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597088 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_2597088 : Nat := 118140960795 + 2597088 * 2 ^ 59
def prefixEnd_2597088 : Nat := 4983230072969 + 3 ^ 40 * 2597088 * 2
def baseEnd_2597088 : Nat := 889036297349360076637477

theorem tailTrace_2597088 : CollatzResearch.WordTrace tailWord_2597088 prefixEnd_2597088 889036297349360076637477 := by
  unfold tailWord_2597088
  simp only [CollatzResearch.WordTrace]
  refine ⟨47361790607600599081451959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63149054143467465441935945 47361790607600599081451959)
  ·
    refine ⟨71042685911400898622177939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47361790607600599081451959 71042685911400898622177939)
    ·
      refine ⟨106564028867101347933266909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71042685911400898622177939 106564028867101347933266909)
      ·
        refine ⟨39961510825163005474975091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106564028867101347933266909 39961510825163005474975091)
        ·
          refine ⟨59942266237744508212462637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39961510825163005474975091 59942266237744508212462637)
          ·
            refine ⟨22478349839154190579673489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59942266237744508212462637 22478349839154190579673489)
            ·
              refine ⟨16858762379365642934755117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22478349839154190579673489 16858762379365642934755117)
              ·
                refine ⟨6322035892262116100533169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16858762379365642934755117 6322035892262116100533169)
                ·
                  refine ⟨4741526919196587075399877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6322035892262116100533169 4741526919196587075399877)
                  ·
                    refine ⟨889036297349360076637477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741526919196587075399877 889036297349360076637477)
                    ·
                      rfl

theorem cell22_2597088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_2597088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597088 prefixEnd_2597088 := by exact prefixLift 2597088
  have htrace : WordTrace (prefixWord ++ tailWord_2597088) baseStart_2597088 baseEnd_2597088 := by
    simpa [prefixWord, tailWord_2597088, baseEnd_2597088] using wordTrace_append hprefix tailTrace_2597088
  have hstable : (prefixWord ++ tailWord_2597088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597088).length < 2 ^ (prefixWord ++ tailWord_2597088).sum := by decide
  have hdescent : baseEnd_2597088 < baseStart_2597088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597103 : List Nat := [1, 1, 2, 1, 6, 3, 8]
def baseStart_2597103 : Nat := 118140960795 + 2597103 * 2 ^ 59
def prefixEnd_2597103 : Nat := 4983230072969 + 3 ^ 40 * 2597103 * 2
def baseEnd_2597103 : Nat := 32927460450218705093053

theorem tailTrace_2597103 : CollatzResearch.WordTrace tailWord_2597103 prefixEnd_2597103 32927460450218705093053 := by
  unfold tailWord_2597103
  simp only [CollatzResearch.WordTrace]
  refine ⟨94724128310146855724699963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63149418873431237149799975 94724128310146855724699963)
  ·
    refine ⟨142086192465220283587049945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94724128310146855724699963 142086192465220283587049945)
    ·
      refine ⟨106564644348915212690287459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142086192465220283587049945 106564644348915212690287459)
      ·
        refine ⟨159846966523372819035431189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106564644348915212690287459 159846966523372819035431189)
        ·
          refine ⟨7492826555783100892285837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159846966523372819035431189 7492826555783100892285837)
          ·
            refine ⟨2809809958418662834607189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7492826555783100892285837 2809809958418662834607189)
            ·
              refine ⟨32927460450218705093053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2809809958418662834607189 32927460450218705093053)
              ·
                rfl

theorem cell22_2597103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 8].length) (baseStart_2597103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597103 prefixEnd_2597103 := by exact prefixLift 2597103
  have htrace : WordTrace (prefixWord ++ tailWord_2597103) baseStart_2597103 baseEnd_2597103 := by
    simpa [prefixWord, tailWord_2597103, baseEnd_2597103] using wordTrace_append hprefix tailTrace_2597103
  have hstable : (prefixWord ++ tailWord_2597103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597103).length < 2 ^ (prefixWord ++ tailWord_2597103).sum := by decide
  have hdescent : baseEnd_2597103 < baseStart_2597103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597169 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 1, 3]
def baseStart_2597169 : Nat := 118140960795 + 2597169 * 2 ^ 59
def prefixEnd_2597169 : Nat := 4983230072969 + 3 ^ 40 * 2597169 * 2
def baseEnd_2597169 : Nat := 889064025304702865362229

theorem tailTrace_2597169 : CollatzResearch.WordTrace tailWord_2597169 prefixEnd_2597169 889064025304702865362229 := by
  unfold tailWord_2597169
  simp only [CollatzResearch.WordTrace]
  refine ⟨94726535527907748996602561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63151023685271832664401707 94726535527907748996602561)
  ·
    refine ⟨71044901645930811747451921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94726535527907748996602561 71044901645930811747451921)
    ·
      refine ⟨53283676234448108810588941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71044901645930811747451921 53283676234448108810588941)
      ·
        refine ⟨19981378587918040803970853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53283676234448108810588941 19981378587918040803970853)
        ·
          refine ⟨3746508485234632650744535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19981378587918040803970853 3746508485234632650744535)
          ·
            refine ⟨5619762727851948976116803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746508485234632650744535 5619762727851948976116803)
            ·
              refine ⟨8429644091777923464175205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619762727851948976116803 8429644091777923464175205)
              ·
                refine ⟨1580558267208360649532851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8429644091777923464175205 1580558267208360649532851)
                ·
                  refine ⟨2370837400812540974299277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580558267208360649532851 2370837400812540974299277)
                  ·
                    refine ⟨889064025304702865362229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370837400812540974299277 889064025304702865362229)
                    ·
                      rfl

theorem cell22_2597169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_2597169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597169 prefixEnd_2597169 := by exact prefixLift 2597169
  have htrace : WordTrace (prefixWord ++ tailWord_2597169) baseStart_2597169 baseEnd_2597169 := by
    simpa [prefixWord, tailWord_2597169, baseEnd_2597169] using wordTrace_append hprefix tailTrace_2597169
  have hstable : (prefixWord ++ tailWord_2597169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597169).length < 2 ^ (prefixWord ++ tailWord_2597169).sum := by decide
  have hdescent : baseEnd_2597169 < baseStart_2597169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597208 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_2597208 : Nat := 118140960795 + 2597208 * 2 ^ 59
def prefixEnd_2597208 : Nat := 4983230072969 + 3 ^ 40 * 2597208 * 2
def baseEnd_2597208 : Nat := 889077375801719763637109

theorem tailTrace_2597208 : CollatzResearch.WordTrace tailWord_2597208 prefixEnd_2597208 889077375801719763637109 := by
  unfold tailWord_2597208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47363978987383229328636139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63151971983177639104848185 47363978987383229328636139)
  ·
    refine ⟨71045968481074843992954209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47363978987383229328636139 71045968481074843992954209)
    ·
      refine ⟨53284476360806132994715657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71045968481074843992954209 53284476360806132994715657)
      ·
        refine ⟨39963357270604599746036743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53284476360806132994715657 39963357270604599746036743)
        ·
          refine ⟨59945035905906899619055115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39963357270604599746036743 59945035905906899619055115)
          ·
            refine ⟨89917553858860349428582673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59945035905906899619055115 89917553858860349428582673)
            ·
              refine ⟨67438165394145262071437005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89917553858860349428582673 67438165394145262071437005)
              ·
                refine ⟨25289312022804473276788877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67438165394145262071437005 25289312022804473276788877)
                ·
                  refine ⟨9483492008551677478795829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25289312022804473276788877 9483492008551677478795829)
                  ·
                    refine ⟨889077375801719763637109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9483492008551677478795829 889077375801719763637109)
                    ·
                      rfl

theorem cell22_2597208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_2597208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597208 prefixEnd_2597208 := by exact prefixLift 2597208
  have htrace : WordTrace (prefixWord ++ tailWord_2597208) baseStart_2597208 baseEnd_2597208 := by
    simpa [prefixWord, tailWord_2597208, baseEnd_2597208] using wordTrace_append hprefix tailTrace_2597208
  have hstable : (prefixWord ++ tailWord_2597208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597208).length < 2 ^ (prefixWord ++ tailWord_2597208).sum := by decide
  have hdescent : baseEnd_2597208 < baseStart_2597208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597225 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_2597225 : Nat := 118140960795 + 2597225 * 2 ^ 59
def prefixEnd_2597225 : Nat := 4983230072969 + 3 ^ 40 * 2597225 * 2
def baseEnd_2597225 : Nat := 889083195249137385962057

theorem tailTrace_2597225 : CollatzResearch.WordTrace tailWord_2597225 prefixEnd_2597225 889083195249137385962057 := by
  unfold tailWord_2597225
  simp only [CollatzResearch.WordTrace]
  refine ⟨94728578015704870560641129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63152385343803247040427419 94728578015704870560641129)
  ·
    refine ⟨71046433511778652920480847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94728578015704870560641129 71046433511778652920480847)
    ·
      refine ⟨106569650267667979380721271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71046433511778652920480847 106569650267667979380721271)
      ·
        refine ⟨159854475401501969071081907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106569650267667979380721271 159854475401501969071081907)
        ·
          refine ⟨239781713102252953606622861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159854475401501969071081907 239781713102252953606622861)
          ·
            refine ⟨89918142413344857602483573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239781713102252953606622861 89918142413344857602483573)
            ·
              refine ⟨8429825851251080400232835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89918142413344857602483573 8429825851251080400232835)
              ·
                refine ⟨12644738776876620600349253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8429825851251080400232835 12644738776876620600349253)
                ·
                  refine ⟨2370888520664366362565485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12644738776876620600349253 2370888520664366362565485)
                  ·
                    refine ⟨889083195249137385962057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370888520664366362565485 889083195249137385962057)
                    ·
                      rfl

theorem cell22_2597225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_2597225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597225 prefixEnd_2597225 := by exact prefixLift 2597225
  have htrace : WordTrace (prefixWord ++ tailWord_2597225) baseStart_2597225 baseEnd_2597225 := by
    simpa [prefixWord, tailWord_2597225, baseEnd_2597225] using wordTrace_append hprefix tailTrace_2597225
  have hstable : (prefixWord ++ tailWord_2597225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597225).length < 2 ^ (prefixWord ++ tailWord_2597225).sum := by decide
  have hdescent : baseEnd_2597225 < baseStart_2597225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597253 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2597253 : Nat := 118140960795 + 2597253 * 2 ^ 59
def prefixEnd_2597253 : Nat := 4983230072969 + 3 ^ 40 * 2597253 * 2
def baseEnd_2597253 : Nat := 889092780221354646261971

theorem tailTrace_2597253 : CollatzResearch.WordTrace tailWord_2597253 prefixEnd_2597253 889092780221354646261971 := by
  unfold tailWord_2597253
  simp only [CollatzResearch.WordTrace]
  refine ⟨94729599259603431342660413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63153066173068954228440275 94729599259603431342660413)
  ·
    refine ⟨35523599722351286753497655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94729599259603431342660413 35523599722351286753497655)
    ·
      refine ⟨53285399583526930130246483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35523599722351286753497655 53285399583526930130246483)
      ·
        refine ⟨79928099375290395195369725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53285399583526930130246483 79928099375290395195369725)
        ·
          refine ⟨29973037265733898198263647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79928099375290395195369725 29973037265733898198263647)
          ·
            refine ⟨44959555898600847297395471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29973037265733898198263647 44959555898600847297395471)
            ·
              refine ⟨67439333847901270946093207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44959555898600847297395471 67439333847901270946093207)
              ·
                refine ⟨101159000771851906419139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67439333847901270946093207 101159000771851906419139811)
                ·
                  refine ⟨151738501157777859628709717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101159000771851906419139811 151738501157777859628709717)
                  ·
                    refine ⟨889092780221354646261971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151738501157777859628709717 889092780221354646261971)
                    ·
                      rfl

theorem cell22_2597253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2597253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597253 prefixEnd_2597253 := by exact prefixLift 2597253
  have htrace : WordTrace (prefixWord ++ tailWord_2597253) baseStart_2597253 baseEnd_2597253 := by
    simpa [prefixWord, tailWord_2597253, baseEnd_2597253] using wordTrace_append hprefix tailTrace_2597253
  have hstable : (prefixWord ++ tailWord_2597253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597253).length < 2 ^ (prefixWord ++ tailWord_2597253).sum := by decide
  have hdescent : baseEnd_2597253 < baseStart_2597253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597293 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2597293 : Nat := 118140960795 + 2597293 * 2 ^ 59
def prefixEnd_2597293 : Nat := 4983230072969 + 3 ^ 40 * 2597293 * 2
def baseEnd_2597293 : Nat := 889106473038807875261849

theorem tailTrace_2597293 : CollatzResearch.WordTrace tailWord_2597293 prefixEnd_2597293 889106473038807875261849 := by
  unfold tailWord_2597293
  simp only [CollatzResearch.WordTrace]
  refine ⟨94731058179458518174116533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63154038786305678782744355 94731058179458518174116533)
  ·
    refine ⟨8881036704324236078823425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94731058179458518174116533 8881036704324236078823425)
    ·
      refine ⟨6660777528243177059117569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8881036704324236078823425 6660777528243177059117569)
      ·
        refine ⟨4995583146182382794338177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6660777528243177059117569 4995583146182382794338177)
        ·
          refine ⟨3746687359636787095753633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4995583146182382794338177 3746687359636787095753633)
          ·
            refine ⟨2810015519727590321815225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746687359636787095753633 2810015519727590321815225)
            ·
              refine ⟨2107511639795692741361419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810015519727590321815225 2107511639795692741361419)
              ·
                refine ⟨3161267459693539112042129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107511639795692741361419 3161267459693539112042129)
                ·
                  refine ⟨2370950594770154334031597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161267459693539112042129 2370950594770154334031597)
                  ·
                    refine ⟨889106473038807875261849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370950594770154334031597 889106473038807875261849)
                    ·
                      rfl

theorem cell22_2597293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2597293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597293 prefixEnd_2597293 := by exact prefixLift 2597293
  have htrace : WordTrace (prefixWord ++ tailWord_2597293) baseStart_2597293 baseEnd_2597293 := by
    simpa [prefixWord, tailWord_2597293, baseEnd_2597293] using wordTrace_append hprefix tailTrace_2597293
  have hstable : (prefixWord ++ tailWord_2597293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597293).length < 2 ^ (prefixWord ++ tailWord_2597293).sum := by decide
  have hdescent : baseEnd_2597293 < baseStart_2597293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597334 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2597334 : Nat := 118140960795 + 2597334 * 2 ^ 59
def prefixEnd_2597334 : Nat := 4983230072969 + 3 ^ 40 * 2597334 * 2
def baseEnd_2597334 : Nat := 296373502725565811662241

theorem tailTrace_2597334 : CollatzResearch.WordTrace tailWord_2597334 prefixEnd_2597334 296373502725565811662241 := by
  unfold tailWord_2597334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5920784598269373886022441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63155035714873321450906037 5920784598269373886022441)
  ·
    refine ⟨4440588448702030414516831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5920784598269373886022441 4440588448702030414516831)
    ·
      refine ⟨6660882673053045621775247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440588448702030414516831 6660882673053045621775247)
      ·
        refine ⟨9991324009579568432662871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6660882673053045621775247 9991324009579568432662871)
        ·
          refine ⟨14986986014369352648994307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9991324009579568432662871 14986986014369352648994307)
          ·
            refine ⟨22480479021554028973491461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14986986014369352648994307 22480479021554028973491461)
            ·
              refine ⟨4215089816541380432529649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22480479021554028973491461 4215089816541380432529649)
              ·
                refine ⟨3161317362406035324397237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215089816541380432529649 3161317362406035324397237)
                ·
                  refine ⟨296373502725565811662241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3161317362406035324397237 296373502725565811662241)
                  ·
                    rfl

theorem cell22_2597334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2597334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597334 prefixEnd_2597334 := by exact prefixLift 2597334
  have htrace : WordTrace (prefixWord ++ tailWord_2597334) baseStart_2597334 baseEnd_2597334 := by
    simpa [prefixWord, tailWord_2597334, baseEnd_2597334] using wordTrace_append hprefix tailTrace_2597334
  have hstable : (prefixWord ++ tailWord_2597334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597334).length < 2 ^ (prefixWord ++ tailWord_2597334).sum := by decide
  have hdescent : baseEnd_2597334 < baseStart_2597334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597345 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 6]
def baseStart_2597345 : Nat := 118140960795 + 2597345 * 2 ^ 59
def prefixEnd_2597345 : Nat := 4983230072969 + 3 ^ 40 * 2597345 * 2
def baseEnd_2597345 : Nat := 296374757900499024320563

theorem tailTrace_2597345 : CollatzResearch.WordTrace tailWord_2597345 prefixEnd_2597345 296374757900499024320563 := by
  unfold tailWord_2597345
  simp only [CollatzResearch.WordTrace]
  refine ⟨94732954775270131055009489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63155303183513420703339659 94732954775270131055009489)
  ·
    refine ⟨71049716081452598291257117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94732954775270131055009489 71049716081452598291257117)
    ·
      refine ⟨26643643530544724359221419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71049716081452598291257117 26643643530544724359221419)
      ·
        refine ⟨39965465295817086538832129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26643643530544724359221419 39965465295817086538832129)
        ·
          refine ⟨29974098971862814904124097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39965465295817086538832129 29974098971862814904124097)
          ·
            refine ⟨22480574228897111178093073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29974098971862814904124097 22480574228897111178093073)
            ·
              refine ⟨16860430671672833383569805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22480574228897111178093073 16860430671672833383569805)
              ·
                refine ⟨6322661501877312518838677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16860430671672833383569805 6322661501877312518838677)
                ·
                  refine ⟨296374757900499024320563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6322661501877312518838677 296374757900499024320563)
                  ·
                    rfl

theorem cell22_2597345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_2597345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597345 prefixEnd_2597345 := by exact prefixLift 2597345
  have htrace : WordTrace (prefixWord ++ tailWord_2597345) baseStart_2597345 baseEnd_2597345 := by
    simpa [prefixWord, tailWord_2597345, baseEnd_2597345] using wordTrace_append hprefix tailTrace_2597345
  have hstable : (prefixWord ++ tailWord_2597345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597345).length < 2 ^ (prefixWord ++ tailWord_2597345).sum := by decide
  have hdescent : baseEnd_2597345 < baseStart_2597345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597375 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 1, 6]
def baseStart_2597375 : Nat := 118140960795 + 2597375 * 2 ^ 59
def prefixEnd_2597375 : Nat := 4983230072969 + 3 ^ 40 * 2597375 * 2
def baseEnd_2597375 : Nat := 889134543314586994711597

theorem tailTrace_2597375 : CollatzResearch.WordTrace tailWord_2597375 prefixEnd_2597375 889134543314586994711597 := by
  unfold tailWord_2597375
  simp only [CollatzResearch.WordTrace]
  refine ⟨94734048965161446178601579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63156032643440964119067719 94734048965161446178601579)
  ·
    refine ⟨142101073447742169267902369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94734048965161446178601579 142101073447742169267902369)
    ·
      refine ⟨106575805085806626950926777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142101073447742169267902369 106575805085806626950926777)
      ·
        refine ⟨79931853814354970213195083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106575805085806626950926777 79931853814354970213195083)
        ·
          refine ⟨119897780721532455319792625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79931853814354970213195083 119897780721532455319792625)
          ·
            refine ⟨89923335541149341489844469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119897780721532455319792625 89923335541149341489844469)
            ·
              refine ⟨8430312706982750764672919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89923335541149341489844469 8430312706982750764672919)
              ·
                refine ⟨12645469060474126147009379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430312706982750764672919 12645469060474126147009379)
                ·
                  refine ⟨18968203590711189220514069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12645469060474126147009379 18968203590711189220514069)
                  ·
                    refine ⟨889134543314586994711597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18968203590711189220514069 889134543314586994711597)
                    ·
                      rfl

theorem cell22_2597375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_2597375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597375 prefixEnd_2597375 := by exact prefixLift 2597375
  have htrace : WordTrace (prefixWord ++ tailWord_2597375) baseStart_2597375 baseEnd_2597375 := by
    simpa [prefixWord, tailWord_2597375, baseEnd_2597375] using wordTrace_append hprefix tailTrace_2597375
  have hstable : (prefixWord ++ tailWord_2597375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597375).length < 2 ^ (prefixWord ++ tailWord_2597375).sum := by decide
  have hdescent : baseEnd_2597375 < baseStart_2597375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597377 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2597377 : Nat := 118140960795 + 2597377 * 2 ^ 59
def prefixEnd_2597377 : Nat := 4983230072969 + 3 ^ 40 * 2597377 * 2
def baseEnd_2597377 : Nat := 889135227955459656161591

theorem tailTrace_2597377 : CollatzResearch.WordTrace tailWord_2597377 prefixEnd_2597377 889135227955459656161591 := by
  unfold tailWord_2597377
  simp only [CollatzResearch.WordTrace]
  refine ⟨94734121911154200520174385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63156081274102800346782923 94734121911154200520174385)
  ·
    refine ⟨71050591433365650390130789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94734121911154200520174385 71050591433365650390130789)
    ·
      refine ⟨13321985893756059448149523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71050591433365650390130789 13321985893756059448149523)
      ·
        refine ⟨19982978840634089172224285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13321985893756059448149523 19982978840634089172224285)
        ·
          refine ⟨7493617065237783439584107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19982978840634089172224285 7493617065237783439584107)
          ·
            refine ⟨11240425597856675159376161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493617065237783439584107 11240425597856675159376161)
            ·
              refine ⟨8430319198392506369532121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11240425597856675159376161 8430319198392506369532121)
              ·
                refine ⟨6322739398794379777149091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8430319198392506369532121 6322739398794379777149091)
                ·
                  refine ⟨9484109098191569665723637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6322739398794379777149091 9484109098191569665723637)
                  ·
                    refine ⟨889135227955459656161591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9484109098191569665723637 889135227955459656161591)
                    ·
                      rfl

theorem cell22_2597377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2597377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597377 prefixEnd_2597377 := by exact prefixLift 2597377
  have htrace : WordTrace (prefixWord ++ tailWord_2597377) baseStart_2597377 baseEnd_2597377 := by
    simpa [prefixWord, tailWord_2597377, baseEnd_2597377] using wordTrace_append hprefix tailTrace_2597377
  have hstable : (prefixWord ++ tailWord_2597377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597377).length < 2 ^ (prefixWord ++ tailWord_2597377).sum := by decide
  have hdescent : baseEnd_2597377 < baseStart_2597377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597396 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2597396 : Nat := 118140960795 + 2597396 * 2 ^ 59
def prefixEnd_2597396 : Nat := 4983230072969 + 3 ^ 40 * 2597396 * 2
def baseEnd_2597396 : Nat := 296380577347916646645511

theorem tailTrace_2597396 : CollatzResearch.WordTrace tailWord_2597396 prefixEnd_2597396 296380577347916646645511 := by
  unfold tailWord_2597396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47367407449042683382558021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63156543265390244510077361 47367407449042683382558021)
  ·
    refine ⟨8881388896695503134229629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47367407449042683382558021 8881388896695503134229629)
    ·
      refine ⟨3330520836260813675336111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8881388896695503134229629 3330520836260813675336111)
      ·
        refine ⟨4995781254391220513004167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330520836260813675336111 4995781254391220513004167)
        ·
          refine ⟨7493671881586830769506251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995781254391220513004167 7493671881586830769506251)
          ·
            refine ⟨11240507822380246154259377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493671881586830769506251 11240507822380246154259377)
            ·
              refine ⟨8430380866785184615694533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11240507822380246154259377 8430380866785184615694533)
              ·
                refine ⟨1580696412522222115442725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8430380866785184615694533 1580696412522222115442725)
                ·
                  refine ⟨296380577347916646645511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580696412522222115442725 296380577347916646645511)
                  ·
                    rfl

theorem cell22_2597396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2597396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597396 prefixEnd_2597396 := by exact prefixLift 2597396
  have htrace : WordTrace (prefixWord ++ tailWord_2597396) baseStart_2597396 baseEnd_2597396 := by
    simpa [prefixWord, tailWord_2597396, baseEnd_2597396] using wordTrace_append hprefix tailTrace_2597396
  have hstable : (prefixWord ++ tailWord_2597396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597396).length < 2 ^ (prefixWord ++ tailWord_2597396).sum := by decide
  have hdescent : baseEnd_2597396 < baseStart_2597396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597411 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 2, 3]
def baseStart_2597411 : Nat := 118140960795 + 2597411 * 2 ^ 59
def prefixEnd_2597411 : Nat := 4983230072969 + 3 ^ 40 * 2597411 * 2
def baseEnd_2597411 : Nat := 889146866850294900811487

theorem tailTrace_2597411 : CollatzResearch.WordTrace tailWord_2597411 prefixEnd_2597411 889146866850294900811487 := by
  unfold tailWord_2597411
  simp only [CollatzResearch.WordTrace]
  refine ⟨94735361993031024326912087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63156907995354016217941391 94735361993031024326912087)
  ·
    refine ⟨142103042989546536490368131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94735361993031024326912087 142103042989546536490368131)
    ·
      refine ⟨213154564484319804735552197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142103042989546536490368131 213154564484319804735552197)
      ·
        refine ⟨39966480840809963387916037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213154564484319804735552197 39966480840809963387916037)
        ·
          refine ⟨7493715157651868135234257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39966480840809963387916037 7493715157651868135234257)
          ·
            refine ⟨5620286368238901101425693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7493715157651868135234257 5620286368238901101425693)
            ·
              refine ⟨2107607388089587913034635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5620286368238901101425693 2107607388089587913034635)
              ·
                refine ⟨3161411082134381869551953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107607388089587913034635 3161411082134381869551953)
                ·
                  refine ⟨2371058311600786402163965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161411082134381869551953 2371058311600786402163965)
                  ·
                    refine ⟨889146866850294900811487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371058311600786402163965 889146866850294900811487)
                    ·
                      rfl

theorem cell22_2597411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 3].length) (baseStart_2597411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597411 prefixEnd_2597411 := by exact prefixLift 2597411
  have htrace : WordTrace (prefixWord ++ tailWord_2597411) baseStart_2597411 baseEnd_2597411 := by
    simpa [prefixWord, tailWord_2597411, baseEnd_2597411] using wordTrace_append hprefix tailTrace_2597411
  have hstable : (prefixWord ++ tailWord_2597411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597411).length < 2 ^ (prefixWord ++ tailWord_2597411).sum := by decide
  have hdescent : baseEnd_2597411 < baseStart_2597411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597420 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_2597420 : Nat := 118140960795 + 2597420 * 2 ^ 59
def prefixEnd_2597420 : Nat := 4983230072969 + 3 ^ 40 * 2597420 * 2
def baseEnd_2597420 : Nat := 889149947734221877336459

theorem tailTrace_2597420 : CollatzResearch.WordTrace tailWord_2597420 prefixEnd_2597420 889149947734221877336459 := by
  unfold tailWord_2597420
  simp only [CollatzResearch.WordTrace]
  refine ⟨47367845124999209431994857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63157126833332279242659809 47367845124999209431994857)
  ·
    refine ⟨35525883843749407073996143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47367845124999209431994857 35525883843749407073996143)
    ·
      refine ⟨53288825765624110610994215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35525883843749407073996143 53288825765624110610994215)
      ·
        refine ⟨79933238648436165916491323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53288825765624110610994215 79933238648436165916491323)
        ·
          refine ⟨119899857972654248874736985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79933238648436165916491323 119899857972654248874736985)
          ·
            refine ⟨89924893479490686656052739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119899857972654248874736985 89924893479490686656052739)
            ·
              refine ⟨134887340219236029984079109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89924893479490686656052739 134887340219236029984079109)
              ·
                refine ⟨25291376291106755622014833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134887340219236029984079109 25291376291106755622014833)
                ·
                  refine ⟨18968532218330066716511125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25291376291106755622014833 18968532218330066716511125)
                  ·
                    refine ⟨889149947734221877336459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18968532218330066716511125 889149947734221877336459)
                    ·
                      rfl

theorem cell22_2597420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_2597420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597420 prefixEnd_2597420 := by exact prefixLift 2597420
  have htrace : WordTrace (prefixWord ++ tailWord_2597420) baseStart_2597420 baseEnd_2597420 := by
    simpa [prefixWord, tailWord_2597420, baseEnd_2597420] using wordTrace_append hprefix tailTrace_2597420
  have hstable : (prefixWord ++ tailWord_2597420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597420).length < 2 ^ (prefixWord ++ tailWord_2597420).sum := by decide
  have hdescent : baseEnd_2597420 < baseStart_2597420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597452 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_2597452 : Nat := 118140960795 + 2597452 * 2 ^ 59
def prefixEnd_2597452 : Nat := 4983230072969 + 3 ^ 40 * 2597452 * 2
def baseEnd_2597452 : Nat := 296386967329394820178787

theorem tailTrace_2597452 : CollatzResearch.WordTrace tailWord_2597452 prefixEnd_2597452 296386967329394820178787 := by
  unfold tailWord_2597452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47368428692941244164577305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63157904923921658886103073 47368428692941244164577305)
  ·
    refine ⟨35526321519705933123432979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47368428692941244164577305 35526321519705933123432979)
    ·
      refine ⟨53289482279558899685149469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35526321519705933123432979 53289482279558899685149469)
      ·
        refine ⟨19983555854834587381931051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53289482279558899685149469 19983555854834587381931051)
        ·
          refine ⟨29975333782251881072896577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19983555854834587381931051 29975333782251881072896577)
          ·
            refine ⟨22481500336688910804672433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29975333782251881072896577 22481500336688910804672433)
            ·
              refine ⟨16861125252516683103504325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22481500336688910804672433 16861125252516683103504325)
              ·
                refine ⟨3161460984846878081907061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16861125252516683103504325 3161460984846878081907061)
                ·
                  refine ⟨296386967329394820178787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3161460984846878081907061 296386967329394820178787)
                  ·
                    rfl

theorem cell22_2597452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_2597452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597452 prefixEnd_2597452 := by exact prefixLift 2597452
  have htrace : WordTrace (prefixWord ++ tailWord_2597452) baseStart_2597452 baseEnd_2597452 := by
    simpa [prefixWord, tailWord_2597452, baseEnd_2597452] using wordTrace_append hprefix tailTrace_2597452
  have hstable : (prefixWord ++ tailWord_2597452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597452).length < 2 ^ (prefixWord ++ tailWord_2597452).sum := by decide
  have hdescent : baseEnd_2597452 < baseStart_2597452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597465 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_2597465 : Nat := 118140960795 + 2597465 * 2 ^ 59
def prefixEnd_2597465 : Nat := 4983230072969 + 3 ^ 40 * 2597465 * 2
def baseEnd_2597465 : Nat := 889165352153856759961321

theorem tailTrace_2597465 : CollatzResearch.WordTrace tailWord_2597465 prefixEnd_2597465 889165352153856759961321 := by
  unfold tailWord_2597465
  simp only [CollatzResearch.WordTrace]
  refine ⟨94737331534835391549377849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63158221023223594366251899 94737331534835391549377849)
  ·
    refine ⟨71052998651126543662033387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94737331534835391549377849 71052998651126543662033387)
    ·
      refine ⟨106579497976689815493050081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71052998651126543662033387 106579497976689815493050081)
      ·
        refine ⟨79934623482517361619787561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106579497976689815493050081 79934623482517361619787561)
        ·
          refine ⟨59950967611888021214840671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79934623482517361619787561 59950967611888021214840671)
          ·
            refine ⟨89926451417832031822261007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59950967611888021214840671 89926451417832031822261007)
            ·
              refine ⟨134889677126748047733391511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89926451417832031822261007 134889677126748047733391511)
              ·
                refine ⟨202334515690122071600087267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134889677126748047733391511 202334515690122071600087267)
                ·
                  refine ⟨303501773535183107400130901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202334515690122071600087267 303501773535183107400130901)
                  ·
                    refine ⟨889165352153856759961321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 303501773535183107400130901 889165352153856759961321)
                    ·
                      rfl

theorem cell22_2597465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_2597465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597465 prefixEnd_2597465 := by exact prefixLift 2597465
  have htrace : WordTrace (prefixWord ++ tailWord_2597465) baseStart_2597465 baseEnd_2597465 := by
    simpa [prefixWord, tailWord_2597465, baseEnd_2597465] using wordTrace_append hprefix tailTrace_2597465
  have hstable : (prefixWord ++ tailWord_2597465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597465).length < 2 ^ (prefixWord ++ tailWord_2597465).sum := by decide
  have hdescent : baseEnd_2597465 < baseStart_2597465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597527 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2597527 : Nat := 118140960795 + 2597527 * 2 ^ 59
def prefixEnd_2597527 : Nat := 4983230072969 + 3 ^ 40 * 2597527 * 2
def baseEnd_2597527 : Nat := 889186576020909264911131

theorem tailTrace_2597527 : CollatzResearch.WordTrace tailWord_2597527 prefixEnd_2597527 889186576020909264911131 := by
  unfold tailWord_2597527
  simp only [CollatzResearch.WordTrace]
  refine ⟨94739592860610776138134835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63159728573740517425423223 94739592860610776138134835)
  ·
    refine ⟨142109389290916164207202253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94739592860610776138134835 142109389290916164207202253)
    ·
      refine ⟨53291020984093561577700845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142109389290916164207202253 53291020984093561577700845)
      ·
        refine ⟨19984132869035085591637817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53291020984093561577700845 19984132869035085591637817)
        ·
          refine ⟨14988099651776314193728363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19984132869035085591637817 14988099651776314193728363)
          ·
            refine ⟨22482149477664471290592545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14988099651776314193728363 22482149477664471290592545)
            ·
              refine ⟨16861612108248353467944409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22482149477664471290592545 16861612108248353467944409)
              ·
                refine ⟨12646209081186265100958307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16861612108248353467944409 12646209081186265100958307)
                ·
                  refine ⟨18969313621779397651437461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12646209081186265100958307 18969313621779397651437461)
                  ·
                    refine ⟨889186576020909264911131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18969313621779397651437461 889186576020909264911131)
                    ·
                      rfl

theorem cell22_2597527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2597527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597527 prefixEnd_2597527 := by exact prefixLift 2597527
  have htrace : WordTrace (prefixWord ++ tailWord_2597527) baseStart_2597527 baseEnd_2597527 := by
    simpa [prefixWord, tailWord_2597527, baseEnd_2597527] using wordTrace_append hprefix tailTrace_2597527
  have hstable : (prefixWord ++ tailWord_2597527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597527).length < 2 ^ (prefixWord ++ tailWord_2597527).sum := by decide
  have hdescent : baseEnd_2597527 < baseStart_2597527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597529 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_2597529 : Nat := 118140960795 + 2597529 * 2 ^ 59
def prefixEnd_2597529 : Nat := 4983230072969 + 3 ^ 40 * 2597529 * 2
def baseEnd_2597529 : Nat := 889187260661781926361125

theorem tailTrace_2597529 : CollatzResearch.WordTrace tailWord_2597529 prefixEnd_2597529 889187260661781926361125 := by
  unfold tailWord_2597529
  simp only [CollatzResearch.WordTrace]
  refine ⟨94739665806603530479707641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63159777204402353653138427 94739665806603530479707641)
  ·
    refine ⟨71054749354952647859780731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94739665806603530479707641 71054749354952647859780731)
    ·
      refine ⟨106582124032428971789671097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71054749354952647859780731 106582124032428971789671097)
      ·
        refine ⟨79936593024321728842253323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106582124032428971789671097 79936593024321728842253323)
        ·
          refine ⟨119904889536482593263379985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79936593024321728842253323 119904889536482593263379985)
          ·
            refine ⟨89928667152361944947534989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119904889536482593263379985 89928667152361944947534989)
            ·
              refine ⟨33723250182135729355325621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89928667152361944947534989 33723250182135729355325621)
              ·
                refine ⟨3161554704575224627061777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33723250182135729355325621 3161554704575224627061777)
                ·
                  refine ⟨2371166028431418470296333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161554704575224627061777 2371166028431418470296333)
                  ·
                    refine ⟨889187260661781926361125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371166028431418470296333 889187260661781926361125)
                    ·
                      rfl

theorem cell22_2597529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_2597529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597529 prefixEnd_2597529 := by exact prefixLift 2597529
  have htrace : WordTrace (prefixWord ++ tailWord_2597529) baseStart_2597529 baseEnd_2597529 := by
    simpa [prefixWord, tailWord_2597529, baseEnd_2597529] using wordTrace_append hprefix tailTrace_2597529
  have hstable : (prefixWord ++ tailWord_2597529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597529).length < 2 ^ (prefixWord ++ tailWord_2597529).sum := by decide
  have hdescent : baseEnd_2597529 < baseStart_2597529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597550 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2597550 : Nat := 118140960795 + 2597550 * 2 ^ 59
def prefixEnd_2597550 : Nat := 4983230072969 + 3 ^ 40 * 2597550 * 2
def baseEnd_2597550 : Nat := 889194449390944871586061

theorem tailTrace_2597550 : CollatzResearch.WordTrace tailWord_2597550 prefixEnd_2597550 889194449390944871586061 := by
  unfold tailWord_2597550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842553967440931383277763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63160287826351634044148069 11842553967440931383277763)
  ·
    refine ⟨17763830951161397074916645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11842553967440931383277763 17763830951161397074916645)
    ·
      refine ⟨3330718303342761951546871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17763830951161397074916645 3330718303342761951546871)
      ·
        refine ⟨4996077455014142927320307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330718303342761951546871 4996077455014142927320307)
        ·
          refine ⟨7494116182521214390980461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4996077455014142927320307 7494116182521214390980461)
          ·
            refine ⟨2810293568445455396617673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7494116182521214390980461 2810293568445455396617673)
            ·
              refine ⟨2107720176334091547463255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810293568445455396617673 2107720176334091547463255)
              ·
                refine ⟨3161580264501137321194883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107720176334091547463255 3161580264501137321194883)
                ·
                  refine ⟨4742370396751705981792325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161580264501137321194883 4742370396751705981792325)
                  ·
                    refine ⟨889194449390944871586061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4742370396751705981792325 889194449390944871586061)
                    ·
                      rfl

theorem cell22_2597550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2597550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597550 prefixEnd_2597550 := by exact prefixLift 2597550
  have htrace : WordTrace (prefixWord ++ tailWord_2597550) baseStart_2597550 baseEnd_2597550 := by
    simpa [prefixWord, tailWord_2597550, baseEnd_2597550] using wordTrace_append hprefix tailTrace_2597550
  have hstable : (prefixWord ++ tailWord_2597550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597550).length < 2 ^ (prefixWord ++ tailWord_2597550).sum := by decide
  have hdescent : baseEnd_2597550 < baseStart_2597550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597664 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_2597664 : Nat := 118140960795 + 2597664 * 2 ^ 59
def prefixEnd_2597664 : Nat := 4983230072969 + 3 ^ 40 * 2597664 * 2
def baseEnd_2597664 : Nat := 889233473920686574235711

theorem tailTrace_2597664 : CollatzResearch.WordTrace tailWord_2597664 prefixEnd_2597664 889233473920686574235711 := by
  unfold tailWord_2597664
  simp only [CollatzResearch.WordTrace]
  refine ⟨47372294830557224267936023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63163059774076299023914697 47372294830557224267936023)
  ·
    refine ⟨71058442245835836401904035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47372294830557224267936023 71058442245835836401904035)
    ·
      refine ⟨106587663368753754602856053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71058442245835836401904035 106587663368753754602856053)
      ·
        refine ⟨9992593440820664494017755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106587663368753754602856053 9992593440820664494017755)
        ·
          refine ⟨14988890161230996741026633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9992593440820664494017755 14988890161230996741026633)
          ·
            refine ⟨11241667620923247555769975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14988890161230996741026633 11241667620923247555769975)
            ·
              refine ⟨16862501431384871333654963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11241667620923247555769975 16862501431384871333654963)
              ·
                refine ⟨25293752147077307000482445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16862501431384871333654963 25293752147077307000482445)
                ·
                  refine ⟨9485157055153990125180917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25293752147077307000482445 9485157055153990125180917)
                  ·
                    refine ⟨889233473920686574235711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9485157055153990125180917 889233473920686574235711)
                    ·
                      rfl

theorem cell22_2597664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_2597664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597664 prefixEnd_2597664 := by exact prefixLift 2597664
  have htrace : WordTrace (prefixWord ++ tailWord_2597664) baseStart_2597664 baseEnd_2597664 := by
    simpa [prefixWord, tailWord_2597664, baseEnd_2597664] using wordTrace_append hprefix tailTrace_2597664
  have hstable : (prefixWord ++ tailWord_2597664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597664).length < 2 ^ (prefixWord ++ tailWord_2597664).sum := by decide
  have hdescent : baseEnd_2597664 < baseStart_2597664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597683 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 4]
def baseStart_2597683 : Nat := 118140960795 + 2597683 * 2 ^ 59
def prefixEnd_2597683 : Nat := 4983230072969 + 3 ^ 40 * 2597683 * 2
def baseEnd_2597683 : Nat := 296413326002992286003551

theorem tailTrace_2597683 : CollatzResearch.WordTrace tailWord_2597683 prefixEnd_2597683 296413326002992286003551 := by
  unfold tailWord_2597683
  simp only [CollatzResearch.WordTrace]
  refine ⟨94745282648045614780813703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63163521765363743187209135 94745282648045614780813703)
  ·
    refine ⟨142117923972068422171220555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94745282648045614780813703 142117923972068422171220555)
    ·
      refine ⟨213176885958102633256830833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142117923972068422171220555 213176885958102633256830833)
      ·
        refine ⟨159882664468576974942623125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213176885958102633256830833 159882664468576974942623125)
        ·
          refine ⟨7494499896964545700435459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159882664468576974942623125 7494499896964545700435459)
          ·
            refine ⟨11241749845446818550653189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494499896964545700435459 11241749845446818550653189)
            ·
              refine ⟨2107828096021278478247473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11241749845446818550653189 2107828096021278478247473)
              ·
                refine ⟨1580871072015958858685605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2107828096021278478247473 1580871072015958858685605)
                ·
                  refine ⟨296413326002992286003551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580871072015958858685605 296413326002992286003551)
                  ·
                    rfl

theorem cell22_2597683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 4].length) (baseStart_2597683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597683 prefixEnd_2597683 := by exact prefixLift 2597683
  have htrace : WordTrace (prefixWord ++ tailWord_2597683) baseStart_2597683 baseEnd_2597683 := by
    simpa [prefixWord, tailWord_2597683, baseEnd_2597683] using wordTrace_append hprefix tailTrace_2597683
  have hstable : (prefixWord ++ tailWord_2597683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597683).length < 2 ^ (prefixWord ++ tailWord_2597683).sum := by decide
  have hdescent : baseEnd_2597683 < baseStart_2597683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597713 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_2597713 : Nat := 118140960795 + 2597713 * 2 ^ 59
def prefixEnd_2597713 : Nat := 4983230072969 + 3 ^ 40 * 2597713 * 2
def baseEnd_2597713 : Nat := 889250247622066779760561

theorem tailTrace_2597713 : CollatzResearch.WordTrace tailWord_2597713 prefixEnd_2597713 889250247622066779760561 := by
  unfold tailWord_2597713
  simp only [CollatzResearch.WordTrace]
  refine ⟨94746376837936929904405793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63164251225291286602937195 94746376837936929904405793)
  ·
    refine ⟨71059782628452697428304345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94746376837936929904405793 71059782628452697428304345)
    ·
      refine ⟨53294836971339523071228259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71059782628452697428304345 53294836971339523071228259)
      ·
        refine ⟨79942255457009284606842389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53294836971339523071228259 79942255457009284606842389)
        ·
          refine ⟨3747293224547310215945737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79942255457009284606842389 3747293224547310215945737)
          ·
            refine ⟨2810469918410482661959303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747293224547310215945737 2810469918410482661959303)
            ·
              refine ⟨4215704877615723992938955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810469918410482661959303 4215704877615723992938955)
              ·
                refine ⟨6323557316423585989408433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4215704877615723992938955 6323557316423585989408433)
                ·
                  refine ⟨4742667987317689492056325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6323557316423585989408433 4742667987317689492056325)
                  ·
                    refine ⟨889250247622066779760561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4742667987317689492056325 889250247622066779760561)
                    ·
                      rfl

theorem cell22_2597713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_2597713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597713 prefixEnd_2597713 := by exact prefixLift 2597713
  have htrace : WordTrace (prefixWord ++ tailWord_2597713) baseStart_2597713 baseEnd_2597713 := by
    simpa [prefixWord, tailWord_2597713, baseEnd_2597713] using wordTrace_append hprefix tailTrace_2597713
  have hstable : (prefixWord ++ tailWord_2597713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597713).length < 2 ^ (prefixWord ++ tailWord_2597713).sum := by decide
  have hdescent : baseEnd_2597713 < baseStart_2597713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597762 : List Nat := [3, 4, 2, 2, 1, 2, 2, 6]
def baseStart_2597762 : Nat := 118140960795 + 2597762 * 2 ^ 59
def prefixEnd_2597762 : Nat := 4983230072969 + 3 ^ 40 * 2597762 * 2
def baseEnd_2597762 : Nat := 98807446813716331698379

theorem tailTrace_2597762 : CollatzResearch.WordTrace tailWord_2597762 prefixEnd_2597762 98807446813716331698379 := by
  unfold tailWord_2597762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23687041003689852818234885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63165442676506274181959693 23687041003689852818234885)
  ·
    refine ⟨4441320188191847403419041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23687041003689852818234885 4441320188191847403419041)
    ·
      refine ⟨3330990141143885552564281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4441320188191847403419041 3330990141143885552564281)
      ·
        refine ⟨2498242605857914164423211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3330990141143885552564281 2498242605857914164423211)
        ·
          refine ⟨3747363908786871246634817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498242605857914164423211 3747363908786871246634817)
          ·
            refine ⟨2810522931590153434976113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747363908786871246634817 2810522931590153434976113)
            ·
              refine ⟨2107892198692615076232085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810522931590153434976113 2107892198692615076232085)
              ·
                refine ⟨98807446813716331698379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2107892198692615076232085 98807446813716331698379)
                ·
                  rfl

theorem cell22_2597762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_2597762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597762 prefixEnd_2597762 := by exact prefixLift 2597762
  have htrace : WordTrace (prefixWord ++ tailWord_2597762) baseStart_2597762 baseEnd_2597762 := by
    simpa [prefixWord, tailWord_2597762, baseEnd_2597762] using wordTrace_append hprefix tailTrace_2597762
  have hstable : (prefixWord ++ tailWord_2597762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597762).length < 2 ^ (prefixWord ++ tailWord_2597762).sum := by decide
  have hdescent : baseEnd_2597762 < baseStart_2597762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597831 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2597831 : Nat := 118140960795 + 2597831 * 2 ^ 59
def prefixEnd_2597831 : Nat := 4983230072969 + 3 ^ 40 * 2597831 * 2
def baseEnd_2597831 : Nat := 889290641433553805310199

theorem tailTrace_2597831 : CollatzResearch.WordTrace tailWord_2597831 prefixEnd_2597831 889290641433553805310199 := by
  unfold tailWord_2597831
  simp only [CollatzResearch.WordTrace]
  refine ⟨94750680651509436057201347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63167120434339624038134231 94750680651509436057201347)
  ·
    refine ⟨142126020977264154085802021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94750680651509436057201347 142126020977264154085802021)
    ·
      refine ⟨26648628933237028891087879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142126020977264154085802021 26648628933237028891087879)
      ·
        refine ⟨39972943399855543336631819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26648628933237028891087879 39972943399855543336631819)
        ·
          refine ⟨59959415099783315004947729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39972943399855543336631819 59959415099783315004947729)
          ·
            refine ⟨44969561324837486253710797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59959415099783315004947729 44969561324837486253710797)
            ·
              refine ⟨16863585496814057345141549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44969561324837486253710797 16863585496814057345141549)
              ·
                refine ⟨6323844561305271504428081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16863585496814057345141549 6323844561305271504428081)
                ·
                  refine ⟨4742883420978953628321061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6323844561305271504428081 4742883420978953628321061)
                  ·
                    refine ⟨889290641433553805310199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4742883420978953628321061 889290641433553805310199)
                    ·
                      rfl

theorem cell22_2597831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2597831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597831 prefixEnd_2597831 := by exact prefixLift 2597831
  have htrace : WordTrace (prefixWord ++ tailWord_2597831) baseStart_2597831 baseEnd_2597831 := by
    simpa [prefixWord, tailWord_2597831, baseEnd_2597831] using wordTrace_append hprefix tailTrace_2597831
  have hstable : (prefixWord ++ tailWord_2597831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597831).length < 2 ^ (prefixWord ++ tailWord_2597831).sum := by decide
  have hdescent : baseEnd_2597831 < baseStart_2597831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597850 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_2597850 : Nat := 118140960795 + 2597850 * 2 ^ 59
def prefixEnd_2597850 : Nat := 4983230072969 + 3 ^ 40 * 2597850 * 2
def baseEnd_2597850 : Nat := 889297145521844089085141

theorem tailTrace_2597850 : CollatzResearch.WordTrace tailWord_2597850 prefixEnd_2597850 889297145521844089085141 := by
  unfold tailWord_2597850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23687843409610150575535751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63167582425627068201428669 23687843409610150575535751)
  ·
    refine ⟨35531765114415225863303627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23687843409610150575535751 35531765114415225863303627)
    ·
      refine ⟨53297647671622838794955441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35531765114415225863303627 53297647671622838794955441)
      ·
        refine ⟨39973235753717129096216581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53297647671622838794955441 39973235753717129096216581)
        ·
          refine ⟨7494981703821961705540609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39973235753717129096216581 7494981703821961705540609)
          ·
            refine ⟨5621236277866471279155457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7494981703821961705540609 5621236277866471279155457)
            ·
              refine ⟨4215927208399853459366593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5621236277866471279155457 4215927208399853459366593)
              ·
                refine ⟨3161945406299890094524945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215927208399853459366593 3161945406299890094524945)
                ·
                  refine ⟨2371459054724917570893709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161945406299890094524945 2371459054724917570893709)
                  ·
                    refine ⟨889297145521844089085141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371459054724917570893709 889297145521844089085141)
                    ·
                      rfl

theorem cell22_2597850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_2597850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597850 prefixEnd_2597850 := by exact prefixLift 2597850
  have htrace : WordTrace (prefixWord ++ tailWord_2597850) baseStart_2597850 baseEnd_2597850 := by
    simpa [prefixWord, tailWord_2597850, baseEnd_2597850] using wordTrace_append hprefix tailTrace_2597850
  have hstable : (prefixWord ++ tailWord_2597850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597850).length < 2 ^ (prefixWord ++ tailWord_2597850).sum := by decide
  have hdescent : baseEnd_2597850 < baseStart_2597850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597863 : List Nat := [1, 1, 5, 2, 2, 3, 1, 7]
def baseStart_2597863 : Nat := 118140960795 + 2597863 * 2 ^ 59
def prefixEnd_2597863 : Nat := 4983230072969 + 3 ^ 40 * 2597863 * 2
def baseEnd_2597863 : Nat := 98811288409724043167789

theorem tailTrace_2597863 : CollatzResearch.WordTrace tailWord_2597863 prefixEnd_2597863 98811288409724043167789 := by
  unfold tailWord_2597863
  simp only [CollatzResearch.WordTrace]
  refine ⟨94751847787393505522366243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63167898524929003681577495 94751847787393505522366243)
  ·
    refine ⟨142127771681090258283549365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94751847787393505522366243 142127771681090258283549365)
    ·
      refine ⟨13324478595102211714082753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142127771681090258283549365 13324478595102211714082753)
      ·
        refine ⟨9993358946326658785562065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13324478595102211714082753 9993358946326658785562065)
        ·
          refine ⟨7495019209744994089171549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9993358946326658785562065 7495019209744994089171549)
          ·
            refine ⟨2810632203654372783439331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7495019209744994089171549 2810632203654372783439331)
            ·
              refine ⟨4215948305481559175158997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810632203654372783439331 4215948305481559175158997)
              ·
                refine ⟨98811288409724043167789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4215948305481559175158997 98811288409724043167789)
                ·
                  rfl

theorem cell22_2597863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 7].length) (baseStart_2597863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597863 prefixEnd_2597863 := by exact prefixLift 2597863
  have htrace : WordTrace (prefixWord ++ tailWord_2597863) baseStart_2597863 baseEnd_2597863 := by
    simpa [prefixWord, tailWord_2597863, baseEnd_2597863] using wordTrace_append hprefix tailTrace_2597863
  have hstable : (prefixWord ++ tailWord_2597863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597863).length < 2 ^ (prefixWord ++ tailWord_2597863).sum := by decide
  have hdescent : baseEnd_2597863 < baseStart_2597863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597936 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_2597936 : Nat := 118140960795 + 2597936 * 2 ^ 59
def prefixEnd_2597936 : Nat := 4983230072969 + 3 ^ 40 * 2597936 * 2
def baseEnd_2597936 : Nat := 296442195026456177144959

theorem tailTrace_2597936 : CollatzResearch.WordTrace tailWord_2597936 prefixEnd_2597936 296442195026456177144959 := by
  unfold tailWord_2597936
  simp only [CollatzResearch.WordTrace]
  refine ⟨47377255158064519494886831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63169673544086025993182441 47377255158064519494886831)
  ·
    refine ⟨71065882737096779242330247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47377255158064519494886831 71065882737096779242330247)
    ·
      refine ⟨106598824105645168863495371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71065882737096779242330247 106598824105645168863495371)
      ·
        refine ⟨159898236158467753295243057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106598824105645168863495371 159898236158467753295243057)
        ·
          refine ⟨119923677118850814971432293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159898236158467753295243057 119923677118850814971432293)
          ·
            refine ⟨22485689459784527807143555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119923677118850814971432293 22485689459784527807143555)
            ·
              refine ⟨33728534189676791710715333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22485689459784527807143555 33728534189676791710715333)
              ·
                refine ⟨6324100160564398445759125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33728534189676791710715333 6324100160564398445759125)
                ·
                  refine ⟨296442195026456177144959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6324100160564398445759125 296442195026456177144959)
                  ·
                    rfl

theorem cell22_2597936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_2597936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597936 prefixEnd_2597936 := by exact prefixLift 2597936
  have htrace : WordTrace (prefixWord ++ tailWord_2597936) baseStart_2597936 baseEnd_2597936 := by
    simpa [prefixWord, tailWord_2597936, baseEnd_2597936] using wordTrace_append hprefix tailTrace_2597936
  have hstable : (prefixWord ++ tailWord_2597936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597936).length < 2 ^ (prefixWord ++ tailWord_2597936).sum := by decide
  have hdescent : baseEnd_2597936 < baseStart_2597936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597951 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_2597951 : Nat := 118140960795 + 2597951 * 2 ^ 59
def prefixEnd_2597951 : Nat := 4983230072969 + 3 ^ 40 * 2597951 * 2
def baseEnd_2597951 : Nat := 889331719885913492309831

theorem tailTrace_2597951 : CollatzResearch.WordTrace tailWord_2597951 prefixEnd_2597951 889331719885913492309831 := by
  unfold tailWord_2597951
  simp only [CollatzResearch.WordTrace]
  refine ⟨94755057411074696551569707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63170038274049797701046471 94755057411074696551569707)
  ·
    refine ⟨142132586116612044827354561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94755057411074696551569707 142132586116612044827354561)
    ·
      refine ⟨106599439587459033620515921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142132586116612044827354561 106599439587459033620515921)
      ·
        refine ⟨79949579690594275215386941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106599439587459033620515921 79949579690594275215386941)
        ·
          refine ⟨29981092383972853205770103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79949579690594275215386941 29981092383972853205770103)
          ·
            refine ⟨44971638575959279808655155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29981092383972853205770103 44971638575959279808655155)
            ·
              refine ⟨67457457863938919712982733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44971638575959279808655155 67457457863938919712982733)
              ·
                refine ⟨25296546698977094892368525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67457457863938919712982733 25296546698977094892368525)
                ·
                  refine ⟨9486205012116410584638197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25296546698977094892368525 9486205012116410584638197)
                  ·
                    refine ⟨889331719885913492309831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9486205012116410584638197 889331719885913492309831)
                    ·
                      rfl

theorem cell22_2597951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_2597951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597951 prefixEnd_2597951 := by exact prefixLift 2597951
  have htrace : WordTrace (prefixWord ++ tailWord_2597951) baseStart_2597951 baseEnd_2597951 := by
    simpa [prefixWord, tailWord_2597951, baseEnd_2597951] using wordTrace_append hprefix tailTrace_2597951
  have hstable : (prefixWord ++ tailWord_2597951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597951).length < 2 ^ (prefixWord ++ tailWord_2597951).sum := by decide
  have hdescent : baseEnd_2597951 < baseStart_2597951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597970 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_2597970 : Nat := 118140960795 + 2597970 * 2 ^ 59
def prefixEnd_2597970 : Nat := 4983230072969 + 3 ^ 40 * 2597970 * 2
def baseEnd_2597970 : Nat := 296446074658067925361591

theorem tailTrace_2597970 : CollatzResearch.WordTrace tailWord_2597970 prefixEnd_2597970 296446074658067925361591 := by
  unfold tailWord_2597970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23688937599501465699127841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63170500265337241864340909 23688937599501465699127841)
  ·
    refine ⟨17766703199626099274345881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23688937599501465699127841 17766703199626099274345881)
    ·
      refine ⟨13325027399719574455759411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17766703199626099274345881 13325027399719574455759411)
      ·
        refine ⟨19987541099579361683639117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325027399719574455759411 19987541099579361683639117)
        ·
          refine ⟨7495327912342260631364669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19987541099579361683639117 7495327912342260631364669)
          ·
            refine ⟨2810747967128347736761751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7495327912342260631364669 2810747967128347736761751)
            ·
              refine ⟨4216121950692521605142627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810747967128347736761751 4216121950692521605142627)
              ·
                refine ⟨6324182926038782407713941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216121950692521605142627 6324182926038782407713941)
                ·
                  refine ⟨296446074658067925361591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6324182926038782407713941 296446074658067925361591)
                  ·
                    rfl

theorem cell22_2597970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_2597970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597970 prefixEnd_2597970 := by exact prefixLift 2597970
  have htrace : WordTrace (prefixWord ++ tailWord_2597970) baseStart_2597970 baseEnd_2597970 := by
    simpa [prefixWord, tailWord_2597970, baseEnd_2597970] using wordTrace_append hprefix tailTrace_2597970
  have hstable : (prefixWord ++ tailWord_2597970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597970).length < 2 ^ (prefixWord ++ tailWord_2597970).sum := by decide
  have hdescent : baseEnd_2597970 < baseStart_2597970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2597998 : List Nat := [4, 1, 2, 2, 1, 2, 2, 8]
def baseStart_2597998 : Nat := 118140960795 + 2597998 * 2 ^ 59
def prefixEnd_2597998 : Nat := 4983230072969 + 3 ^ 40 * 2597998 * 2
def baseEnd_2597998 : Nat := 98816423216269004042743

theorem tailTrace_2597998 : CollatzResearch.WordTrace tailWord_2597998 prefixEnd_2597998 98816423216269004042743 := by
  unfold tailWord_2597998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844596455238052947316331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63171181094602949052353765 11844596455238052947316331)
  ·
    refine ⟨17766894682857079420974497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11844596455238052947316331 17766894682857079420974497)
    ·
      refine ⟨13325171012142809565730873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17766894682857079420974497 13325171012142809565730873)
      ·
        refine ⟨9993878259107107174298155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13325171012142809565730873 9993878259107107174298155)
        ·
          refine ⟨14990817388660660761447233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9993878259107107174298155 14990817388660660761447233)
          ·
            refine ⟨11243113041495495571085425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14990817388660660761447233 11243113041495495571085425)
            ·
              refine ⟨8432334781121621678314069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11243113041495495571085425 8432334781121621678314069)
              ·
                refine ⟨98816423216269004042743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8432334781121621678314069 98816423216269004042743)
                ·
                  rfl

theorem cell22_2597998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_2597998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2597998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2597998 prefixEnd_2597998 := by exact prefixLift 2597998
  have htrace : WordTrace (prefixWord ++ tailWord_2597998) baseStart_2597998 baseEnd_2597998 := by
    simpa [prefixWord, tailWord_2597998, baseEnd_2597998] using wordTrace_append hprefix tailTrace_2597998
  have hstable : (prefixWord ++ tailWord_2597998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2597998).length < 2 ^ (prefixWord ++ tailWord_2597998).sum := by decide
  have hdescent : baseEnd_2597998 < baseStart_2597998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2597998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598011 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_2598011 : Nat := 118140960795 + 2598011 * 2 ^ 59
def prefixEnd_2598011 : Nat := 4983230072969 + 3 ^ 40 * 2598011 * 2
def baseEnd_2598011 : Nat := 889352259112093335809647

theorem tailTrace_2598011 : CollatzResearch.WordTrace tailWord_2598011 prefixEnd_2598011 889352259112093335809647 := by
  unfold tailWord_2598011
  simp only [CollatzResearch.WordTrace]
  refine ⟨94757245790857326798753887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63171497193904884532502591 94757245790857326798753887)
  ·
    refine ⟨142135868686285990198130831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94757245790857326798753887 142135868686285990198130831)
    ·
      refine ⟨213203803029428985297196247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142135868686285990198130831 213203803029428985297196247)
      ·
        refine ⟨319805704544143477945794371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213203803029428985297196247 319805704544143477945794371)
        ·
          refine ⟨479708556816215216918691557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319805704544143477945794371 479708556816215216918691557)
          ·
            refine ⟨89945354403040353172254667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 479708556816215216918691557 89945354403040353172254667)
            ·
              refine ⟨134918031604560529758382001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89945354403040353172254667 134918031604560529758382001)
              ·
                refine ⟨101188523703420397318786501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134918031604560529758382001 101188523703420397318786501)
                ·
                  refine ⟨18972848194391324497272469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101188523703420397318786501 18972848194391324497272469)
                  ·
                    refine ⟨889352259112093335809647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18972848194391324497272469 889352259112093335809647)
                    ·
                      rfl

theorem cell22_2598011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_2598011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598011 prefixEnd_2598011 := by exact prefixLift 2598011
  have htrace : WordTrace (prefixWord ++ tailWord_2598011) baseStart_2598011 baseEnd_2598011 := by
    simpa [prefixWord, tailWord_2598011, baseEnd_2598011] using wordTrace_append hprefix tailTrace_2598011
  have hstable : (prefixWord ++ tailWord_2598011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598011).length < 2 ^ (prefixWord ++ tailWord_2598011).sum := by decide
  have hdescent : baseEnd_2598011 < baseStart_2598011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598047 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 3, 3]
def baseStart_2598047 : Nat := 118140960795 + 2598047 * 2 ^ 59
def prefixEnd_2598047 : Nat := 4983230072969 + 3 ^ 40 * 2598047 * 2
def baseEnd_2598047 : Nat := 889364582647801241909537

theorem tailTrace_2598047 : CollatzResearch.WordTrace tailWord_2598047 prefixEnd_2598047 889364582647801241909537 := by
  unfold tailWord_2598047
  simp only [CollatzResearch.WordTrace]
  refine ⟨94758558818726904947064395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63172372545817936631376263 94758558818726904947064395)
  ·
    refine ⟨142137838228090357420596593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94758558818726904947064395 142137838228090357420596593)
    ·
      refine ⟨106603378671067768065447445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142137838228090357420596593 106603378671067768065447445)
      ·
        refine ⟨4997033375206301628067849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106603378671067768065447445 4997033375206301628067849)
        ·
          refine ⟨3747775031404726221050887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997033375206301628067849 3747775031404726221050887)
          ·
            refine ⟨5621662547107089331576331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747775031404726221050887 5621662547107089331576331)
            ·
              refine ⟨8432493820660633997364497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621662547107089331576331 8432493820660633997364497)
              ·
                refine ⟨6324370365495475498023373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8432493820660633997364497 6324370365495475498023373)
                ·
                  refine ⟨2371638887060803311758765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6324370365495475498023373 2371638887060803311758765)
                  ·
                    refine ⟨889364582647801241909537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371638887060803311758765 889364582647801241909537)
                    ·
                      rfl

theorem cell22_2598047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_2598047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598047 prefixEnd_2598047 := by exact prefixLift 2598047
  have htrace : WordTrace (prefixWord ++ tailWord_2598047) baseStart_2598047 baseEnd_2598047 := by
    simpa [prefixWord, tailWord_2598047, baseEnd_2598047] using wordTrace_append hprefix tailTrace_2598047
  have hstable : (prefixWord ++ tailWord_2598047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598047).length < 2 ^ (prefixWord ++ tailWord_2598047).sum := by decide
  have hdescent : baseEnd_2598047 < baseStart_2598047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598088 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_2598088 : Nat := 118140960795 + 2598088 * 2 ^ 59
def prefixEnd_2598088 : Nat := 4983230072969 + 3 ^ 40 * 2598088 * 2
def baseEnd_2598088 : Nat := 296459539261896933878137

theorem tailTrace_2598088 : CollatzResearch.WordTrace tailWord_2598088 prefixEnd_2598088 296459539261896933878137 := by
  unfold tailWord_2598088
  simp only [CollatzResearch.WordTrace]
  refine ⟨47380027105789184474653459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63173369474385579299537945 47380027105789184474653459)
  ·
    refine ⟨71070040658683776711980189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47380027105789184474653459 71070040658683776711980189)
    ·
      refine ⟨26651265247006416266992571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71070040658683776711980189 26651265247006416266992571)
      ·
        refine ⟨39976897870509624400488857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26651265247006416266992571 39976897870509624400488857)
        ·
          refine ⟨29982673402882218300366643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39976897870509624400488857 29982673402882218300366643)
          ·
            refine ⟨44974010104323327450549965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29982673402882218300366643 44974010104323327450549965)
            ·
              refine ⟨16865253789121247793956237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44974010104323327450549965 16865253789121247793956237)
              ·
                refine ⟨6324470170920467922733589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16865253789121247793956237 6324470170920467922733589)
                ·
                  refine ⟨296459539261896933878137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6324470170920467922733589 296459539261896933878137)
                  ·
                    rfl

theorem cell22_2598088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_2598088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598088 prefixEnd_2598088 := by exact prefixLift 2598088
  have htrace : WordTrace (prefixWord ++ tailWord_2598088) baseStart_2598088 baseEnd_2598088 := by
    simpa [prefixWord, tailWord_2598088, baseEnd_2598088] using wordTrace_append hprefix tailTrace_2598088
  have hstable : (prefixWord ++ tailWord_2598088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598088).length < 2 ^ (prefixWord ++ tailWord_2598088).sum := by decide
  have hdescent : baseEnd_2598088 < baseStart_2598088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598120 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_2598120 : Nat := 118140960795 + 2598120 * 2 ^ 59
def prefixEnd_2598120 : Nat := 4983230072969 + 3 ^ 40 * 2598120 * 2
def baseEnd_2598120 : Nat := 889389572039653384834313

theorem tailTrace_2598120 : CollatzResearch.WordTrace tailWord_2598120 prefixEnd_2598120 889389572039653384834313 := by
  unfold tailWord_2598120
  simp only [CollatzResearch.WordTrace]
  refine ⟨47380610673731219207235907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63174147564974958942981209 47380610673731219207235907)
  ·
    refine ⟨71070916010596828810853861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47380610673731219207235907 71070916010596828810853861)
    ·
      refine ⟨13325796751986905402035099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71070916010596828810853861 13325796751986905402035099)
      ·
        refine ⟨19988695127980358103052649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325796751986905402035099 19988695127980358103052649)
        ·
          refine ⟨14991521345985268577289487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19988695127980358103052649 14991521345985268577289487)
          ·
            refine ⟨22487282018977902865934231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14991521345985268577289487 22487282018977902865934231)
            ·
              refine ⟨33730923028466854298901347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22487282018977902865934231 33730923028466854298901347)
              ·
                refine ⟨50596384542700281448352021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33730923028466854298901347 50596384542700281448352021)
                ·
                  refine ⟨2371705525439075692891501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50596384542700281448352021 2371705525439075692891501)
                  ·
                    refine ⟨889389572039653384834313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371705525439075692891501 889389572039653384834313)
                    ·
                      rfl

theorem cell22_2598120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_2598120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598120 prefixEnd_2598120 := by exact prefixLift 2598120
  have htrace : WordTrace (prefixWord ++ tailWord_2598120) baseStart_2598120 baseEnd_2598120 := by
    simpa [prefixWord, tailWord_2598120, baseEnd_2598120] using wordTrace_append hprefix tailTrace_2598120
  have hstable : (prefixWord ++ tailWord_2598120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598120).length < 2 ^ (prefixWord ++ tailWord_2598120).sum := by decide
  have hdescent : baseEnd_2598120 < baseStart_2598120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598122 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_2598122 : Nat := 118140960795 + 2598122 * 2 ^ 59
def prefixEnd_2598122 : Nat := 4983230072969 + 3 ^ 40 * 2598122 * 2
def baseEnd_2598122 : Nat := 296463418893508682094769

theorem tailTrace_2598122 : CollatzResearch.WordTrace tailWord_2598122 prefixEnd_2598122 296463418893508682094769 := by
  unfold tailWord_2598122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690323573363798189011155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63174196195636795170696413 23690323573363798189011155)
  ·
    refine ⟨35535485360045697283516733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23690323573363798189011155 35535485360045697283516733)
    ·
      refine ⟨13325807010017136481318775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35535485360045697283516733 13325807010017136481318775)
      ·
        refine ⟨19988710515025704721978163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325807010017136481318775 19988710515025704721978163)
        ·
          refine ⟨29983065772538557082967245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19988710515025704721978163 29983065772538557082967245)
          ·
            refine ⟨11243649664701958906112717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29983065772538557082967245 11243649664701958906112717)
            ·
              refine ⟨4216368624263234589792269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11243649664701958906112717 4216368624263234589792269)
              ·
                refine ⟨1581138234098712971172101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4216368624263234589792269 1581138234098712971172101)
                ·
                  refine ⟨296463418893508682094769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581138234098712971172101 296463418893508682094769)
                  ·
                    rfl

theorem cell22_2598122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_2598122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598122 prefixEnd_2598122 := by exact prefixLift 2598122
  have htrace : WordTrace (prefixWord ++ tailWord_2598122) baseStart_2598122 baseEnd_2598122 := by
    simpa [prefixWord, tailWord_2598122, baseEnd_2598122] using wordTrace_append hprefix tailTrace_2598122
  have hstable : (prefixWord ++ tailWord_2598122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598122).length < 2 ^ (prefixWord ++ tailWord_2598122).sum := by decide
  have hdescent : baseEnd_2598122 < baseStart_2598122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598165 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_2598165 : Nat := 118140960795 + 2598165 * 2 ^ 59
def prefixEnd_2598165 : Nat := 4983230072969 + 3 ^ 40 * 2598165 * 2
def baseEnd_2598165 : Nat := 889404976459288267459175

theorem tailTrace_2598165 : CollatzResearch.WordTrace tailWord_2598165 prefixEnd_2598165 889404976459288267459175 := by
  unfold tailWord_2598165
  simp only [CollatzResearch.WordTrace]
  refine ⟨94762862632299411099859949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63175241754866274066573299 94762862632299411099859949)
  ·
    refine ⟨35536073487112279162447481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94762862632299411099859949 35536073487112279162447481)
    ·
      refine ⟨26652055115334209371835611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35536073487112279162447481 26652055115334209371835611)
      ·
        refine ⟨39978082673001314057753417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26652055115334209371835611 39978082673001314057753417)
        ·
          refine ⟨29983562004750985543315063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39978082673001314057753417 29983562004750985543315063)
          ·
            refine ⟨44975343007126478314972595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29983562004750985543315063 44975343007126478314972595)
            ·
              refine ⟨67463014510689717472458893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44975343007126478314972595 67463014510689717472458893)
              ·
                refine ⟨25298630441508644052172085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67463014510689717472458893 25298630441508644052172085)
                ·
                  refine ⟨2371746603891435379891133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25298630441508644052172085 2371746603891435379891133)
                  ·
                    refine ⟨889404976459288267459175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371746603891435379891133 889404976459288267459175)
                    ·
                      rfl

theorem cell22_2598165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_2598165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598165 prefixEnd_2598165 := by exact prefixLift 2598165
  have htrace : WordTrace (prefixWord ++ tailWord_2598165) baseStart_2598165 baseEnd_2598165 := by
    simpa [prefixWord, tailWord_2598165, baseEnd_2598165] using wordTrace_append hprefix tailTrace_2598165
  have hstable : (prefixWord ++ tailWord_2598165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598165).length < 2 ^ (prefixWord ++ tailWord_2598165).sum := by decide
  have hdescent : baseEnd_2598165 < baseStart_2598165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598195 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 5]
def baseStart_2598195 : Nat := 118140960795 + 2598195 * 2 ^ 59
def prefixEnd_2598195 : Nat := 4983230072969 + 3 ^ 40 * 2598195 * 2
def baseEnd_2598195 : Nat := 296471748690792729736361

theorem tailTrace_2598195 : CollatzResearch.WordTrace tailWord_2598195 prefixEnd_2598195 296471748690792729736361 := by
  unfold tailWord_2598195
  simp only [CollatzResearch.WordTrace]
  refine ⟨94763956822190726223452039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63175971214793817482301359 94763956822190726223452039)
  ·
    refine ⟨142145935233286089335178059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94763956822190726223452039 142145935233286089335178059)
    ·
      refine ⟨213218902849929134002767089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142145935233286089335178059 213218902849929134002767089)
      ·
        refine ⟨159914177137446850502075317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213218902849929134002767089 159914177137446850502075317)
        ·
          refine ⟨14991954106635642234569561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159914177137446850502075317 14991954106635642234569561)
          ·
            refine ⟨11243965579976731675927171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14991954106635642234569561 11243965579976731675927171)
            ·
              refine ⟨16865948369965097513890757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11243965579976731675927171 16865948369965097513890757)
              ·
                refine ⟨3162365319368455783854517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16865948369965097513890757 3162365319368455783854517)
                ·
                  refine ⟨296471748690792729736361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162365319368455783854517 296471748690792729736361)
                  ·
                    rfl

theorem cell22_2598195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 5].length) (baseStart_2598195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598195 prefixEnd_2598195 := by exact prefixLift 2598195
  have htrace : WordTrace (prefixWord ++ tailWord_2598195) baseStart_2598195 baseEnd_2598195 := by
    simpa [prefixWord, tailWord_2598195, baseEnd_2598195] using wordTrace_append hprefix tailTrace_2598195
  have hstable : (prefixWord ++ tailWord_2598195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598195).length < 2 ^ (prefixWord ++ tailWord_2598195).sum := by decide
  have hdescent : baseEnd_2598195 < baseStart_2598195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598225 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2598225 : Nat := 118140960795 + 2598225 * 2 ^ 59
def prefixEnd_2598225 : Nat := 4983230072969 + 3 ^ 40 * 2598225 * 2
def baseEnd_2598225 : Nat := 889425515685468110958991

theorem tailTrace_2598225 : CollatzResearch.WordTrace tailWord_2598225 prefixEnd_2598225 889425515685468110958991 := by
  unfold tailWord_2598225
  simp only [CollatzResearch.WordTrace]
  refine ⟨94765051012082041347044129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63176700674721360898029419 94765051012082041347044129)
  ·
    refine ⟨71073788259061531010283097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94765051012082041347044129 71073788259061531010283097)
    ·
      refine ⟨53305341194296148257712323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71073788259061531010283097 53305341194296148257712323)
      ·
        refine ⟨79958011791444222386568485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53305341194296148257712323 79958011791444222386568485)
        ·
          refine ⟨14992127210895791697481591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79958011791444222386568485 14992127210895791697481591)
          ·
            refine ⟨22488190816343687546222387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14992127210895791697481591 22488190816343687546222387)
            ·
              refine ⟨33732286224515531319333581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22488190816343687546222387 33732286224515531319333581)
              ·
                refine ⟨12649607334193324244750093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33732286224515531319333581 12649607334193324244750093)
                ·
                  refine ⟨4743602750322496591781285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12649607334193324244750093 4743602750322496591781285)
                  ·
                    refine ⟨889425515685468110958991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4743602750322496591781285 889425515685468110958991)
                    ·
                      rfl

theorem cell22_2598225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2598225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598225 prefixEnd_2598225 := by exact prefixLift 2598225
  have htrace : WordTrace (prefixWord ++ tailWord_2598225) baseStart_2598225 baseEnd_2598225 := by
    simpa [prefixWord, tailWord_2598225, baseEnd_2598225] using wordTrace_append hprefix tailTrace_2598225
  have hstable : (prefixWord ++ tailWord_2598225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598225).length < 2 ^ (prefixWord ++ tailWord_2598225).sum := by decide
  have hdescent : baseEnd_2598225 < baseStart_2598225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598257 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 4]
def baseStart_2598257 : Nat := 118140960795 + 2598257 * 2 ^ 59
def prefixEnd_2598257 : Nat := 4983230072969 + 3 ^ 40 * 2598257 * 2
def baseEnd_2598257 : Nat := 296478823313143564719631

theorem tailTrace_2598257 : CollatzResearch.WordTrace tailWord_2598257 prefixEnd_2598257 296478823313143564719631 := by
  unfold tailWord_2598257
  simp only [CollatzResearch.WordTrace]
  refine ⟨94766218147966110812209025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63177478765310740541472683 94766218147966110812209025)
  ·
    refine ⟨71074663610974583109156769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94766218147966110812209025 71074663610974583109156769)
    ·
      refine ⟨53305997708230937331867577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71074663610974583109156769 53305997708230937331867577)
      ·
        refine ⟨39979498281173202998900683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53305997708230937331867577 39979498281173202998900683)
        ·
          refine ⟨59969247421759804498351025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39979498281173202998900683 59969247421759804498351025)
          ·
            refine ⟨44976935566319853373763269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59969247421759804498351025 44976935566319853373763269)
            ·
              refine ⟨8433175418684972507580613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44976935566319853373763269 8433175418684972507580613)
              ·
                refine ⟨1581220391003432345171365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8433175418684972507580613 1581220391003432345171365)
                ·
                  refine ⟨296478823313143564719631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581220391003432345171365 296478823313143564719631)
                  ·
                    rfl

theorem cell22_2598257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_2598257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598257 prefixEnd_2598257 := by exact prefixLift 2598257
  have htrace : WordTrace (prefixWord ++ tailWord_2598257) baseStart_2598257 baseEnd_2598257 := by
    simpa [prefixWord, tailWord_2598257, baseEnd_2598257] using wordTrace_append hprefix tailTrace_2598257
  have hstable : (prefixWord ++ tailWord_2598257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598257).length < 2 ^ (prefixWord ++ tailWord_2598257).sum := by decide
  have hdescent : baseEnd_2598257 < baseStart_2598257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598272 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_2598272 : Nat := 118140960795 + 2598272 * 2 ^ 59
def prefixEnd_2598272 : Nat := 4983230072969 + 3 ^ 40 * 2598272 * 2
def baseEnd_2598272 : Nat := 889441604745975655033847

theorem tailTrace_2598272 : CollatzResearch.WordTrace tailWord_2598272 prefixEnd_2598272 889441604745975655033847 := by
  unfold tailWord_2598272
  simp only [CollatzResearch.WordTrace]
  refine ⟨47383382621455884187002535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63177843495274512249336713 47383382621455884187002535)
  ·
    refine ⟨71075073932183826280503803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47383382621455884187002535 71075073932183826280503803)
    ·
      refine ⟨106612610898275739420755705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71075073932183826280503803 106612610898275739420755705)
      ·
        refine ⟨79959458173706804565566779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106612610898275739420755705 79959458173706804565566779)
        ·
          refine ⟨119939187260560206848350169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79959458173706804565566779 119939187260560206848350169)
          ·
            refine ⟨89954390445420155136262627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119939187260560206848350169 89954390445420155136262627)
            ·
              refine ⟨134931585668130232704393941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89954390445420155136262627 134931585668130232704393941)
              ·
                refine ⟨3162459039096802329009233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134931585668130232704393941 3162459039096802329009233)
                ·
                  refine ⟨2371844279322601746756925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162459039096802329009233 2371844279322601746756925)
                  ·
                    refine ⟨889441604745975655033847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371844279322601746756925 889441604745975655033847)
                    ·
                      rfl

theorem cell22_2598272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_2598272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598272 prefixEnd_2598272 := by exact prefixLift 2598272
  have htrace : WordTrace (prefixWord ++ tailWord_2598272) baseStart_2598272 baseEnd_2598272 := by
    simpa [prefixWord, tailWord_2598272, baseEnd_2598272] using wordTrace_append hprefix tailTrace_2598272
  have hstable : (prefixWord ++ tailWord_2598272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598272).length < 2 ^ (prefixWord ++ tailWord_2598272).sum := by decide
  have hdescent : baseEnd_2598272 < baseStart_2598272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598274 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2598274 : Nat := 118140960795 + 2598274 * 2 ^ 59
def prefixEnd_2598274 : Nat := 4983230072969 + 3 ^ 40 * 2598274 * 2
def baseEnd_2598274 : Nat := 296480763128949438827947

theorem tailTrace_2598274 : CollatzResearch.WordTrace tailWord_2598274 prefixEnd_2598274 296480763128949438827947 := by
  unfold tailWord_2598274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23691709547226130678894469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63177892125936348477051917 23691709547226130678894469)
  ·
    refine ⟨4442195540104899502292713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23691709547226130678894469 4442195540104899502292713)
    ·
      refine ⟨3331646655078674626719535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4442195540104899502292713 3331646655078674626719535)
      ·
        refine ⟨4997469982618011940079303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3331646655078674626719535 4997469982618011940079303)
        ·
          refine ⟨7496204973927017910118955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997469982618011940079303 7496204973927017910118955)
          ·
            refine ⟨11244307460890526865178433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496204973927017910118955 11244307460890526865178433)
            ·
              refine ⟨8433230595667895148883825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11244307460890526865178433 8433230595667895148883825)
              ·
                refine ⟨6324922946750921361662869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433230595667895148883825 6324922946750921361662869)
                ·
                  refine ⟨296480763128949438827947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6324922946750921361662869 296480763128949438827947)
                  ·
                    rfl

theorem cell22_2598274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2598274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598274 prefixEnd_2598274 := by exact prefixLift 2598274
  have htrace : WordTrace (prefixWord ++ tailWord_2598274) baseStart_2598274 baseEnd_2598274 := by
    simpa [prefixWord, tailWord_2598274, baseEnd_2598274] using wordTrace_append hprefix tailTrace_2598274
  have hstable : (prefixWord ++ tailWord_2598274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598274).length < 2 ^ (prefixWord ++ tailWord_2598274).sum := by decide
  have hdescent : baseEnd_2598274 < baseStart_2598274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598345 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_2598345 : Nat := 118140960795 + 2598345 * 2 ^ 59
def prefixEnd_2598345 : Nat := 4983230072969 + 3 ^ 40 * 2598345 * 2
def baseEnd_2598345 : Nat := 889466594137827797958623

theorem tailTrace_2598345 : CollatzResearch.WordTrace tailWord_2598345 prefixEnd_2598345 889466594137827797958623 := by
  unfold tailWord_2598345
  simp only [CollatzResearch.WordTrace]
  refine ⟨94769427771647301841412489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63179618514431534560941659 94769427771647301841412489)
  ·
    refine ⟨71077070828735476381059367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94769427771647301841412489 71077070828735476381059367)
    ·
      refine ⟨106615606243103214571589051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71077070828735476381059367 106615606243103214571589051)
      ·
        refine ⟨159923409364654821857383577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106615606243103214571589051 159923409364654821857383577)
        ·
          refine ⟨119942557023491116393037683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159923409364654821857383577 119942557023491116393037683)
          ·
            refine ⟨179913835535236674589556525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119942557023491116393037683 179913835535236674589556525)
            ·
              refine ⟨67467688325713752971083697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179913835535236674589556525 67467688325713752971083697)
              ·
                refine ⟨50600766244285314728312773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67467688325713752971083697 50600766244285314728312773)
                ·
                  refine ⟨9487643670803496511558645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50600766244285314728312773 9487643670803496511558645)
                  ·
                    refine ⟨889466594137827797958623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9487643670803496511558645 889466594137827797958623)
                    ·
                      rfl

theorem cell22_2598345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_2598345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598345 prefixEnd_2598345 := by exact prefixLift 2598345
  have htrace : WordTrace (prefixWord ++ tailWord_2598345) baseStart_2598345 baseEnd_2598345 := by
    simpa [prefixWord, tailWord_2598345, baseEnd_2598345] using wordTrace_append hprefix tailTrace_2598345
  have hstable : (prefixWord ++ tailWord_2598345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598345).length < 2 ^ (prefixWord ++ tailWord_2598345).sum := by decide
  have hdescent : baseEnd_2598345 < baseStart_2598345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598392 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_2598392 : Nat := 118140960795 + 2598392 * 2 ^ 59
def prefixEnd_2598392 : Nat := 4983230072969 + 3 ^ 40 * 2598392 * 2
def baseEnd_2598392 : Nat := 296494227732778447344493

theorem tailTrace_2598392 : CollatzResearch.WordTrace tailWord_2598392 prefixEnd_2598392 296494227732778447344493 := by
  unfold tailWord_2598392
  simp only [CollatzResearch.WordTrace]
  refine ⟨47385571001238514434186715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63180761334984685912248953 47385571001238514434186715)
  ·
    refine ⟨71078356501857771651280073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47385571001238514434186715 71078356501857771651280073)
    ·
      refine ⟨53308767376393328738460055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71078356501857771651280073 53308767376393328738460055)
      ·
        refine ⟨79963151064589993107690083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53308767376393328738460055 79963151064589993107690083)
        ·
          refine ⟨119944726596884989661535125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79963151064589993107690083 119944726596884989661535125)
          ·
            refine ⟨5622409059228983890384459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119944726596884989661535125 5622409059228983890384459)
            ·
              refine ⟨8433613588843475835576689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622409059228983890384459 8433613588843475835576689)
              ·
                refine ⟨6325210191632606876682517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433613588843475835576689 6325210191632606876682517)
                ·
                  refine ⟨296494227732778447344493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6325210191632606876682517 296494227732778447344493)
                  ·
                    rfl

theorem cell22_2598392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_2598392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598392 prefixEnd_2598392 := by exact prefixLift 2598392
  have htrace : WordTrace (prefixWord ++ tailWord_2598392) baseStart_2598392 baseEnd_2598392 := by
    simpa [prefixWord, tailWord_2598392, baseEnd_2598392] using wordTrace_append hprefix tailTrace_2598392
  have hstable : (prefixWord ++ tailWord_2598392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598392).length < 2 ^ (prefixWord ++ tailWord_2598392).sum := by decide
  have hdescent : baseEnd_2598392 < baseStart_2598392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598409 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 4]
def baseStart_2598409 : Nat := 118140960795 + 2598409 * 2 ^ 59
def prefixEnd_2598409 : Nat := 4983230072969 + 3 ^ 40 * 2598409 * 2
def baseEnd_2598409 : Nat := 296496167548584321452809

theorem tailTrace_2598409 : CollatzResearch.WordTrace tailWord_2598409 prefixEnd_2598409 296496167548584321452809 := by
  unfold tailWord_2598409
  simp only [CollatzResearch.WordTrace]
  refine ⟨94771762043415440771742281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63181174695610293847828187 94771762043415440771742281)
  ·
    refine ⟨71078821532561580578806711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94771762043415440771742281 71078821532561580578806711)
    ·
      refine ⟨106618232298842370868210067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71078821532561580578806711 106618232298842370868210067)
      ·
        refine ⟨159927348448263556302315101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106618232298842370868210067 159927348448263556302315101)
        ·
          refine ⟨59972755668098833613368163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159927348448263556302315101 59972755668098833613368163)
          ·
            refine ⟨89959133502148250420052245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59972755668098833613368163 89959133502148250420052245)
            ·
              refine ⟨4216834382913199238439949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89959133502148250420052245 4216834382913199238439949)
              ·
                refine ⟨1581312893592449714414981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4216834382913199238439949 1581312893592449714414981)
                ·
                  refine ⟨296496167548584321452809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581312893592449714414981 296496167548584321452809)
                  ·
                    rfl

theorem cell22_2598409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_2598409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598409 prefixEnd_2598409 := by exact prefixLift 2598409
  have htrace : WordTrace (prefixWord ++ tailWord_2598409) baseStart_2598409 baseEnd_2598409 := by
    simpa [prefixWord, tailWord_2598409, baseEnd_2598409] using wordTrace_append hprefix tailTrace_2598409
  have hstable : (prefixWord ++ tailWord_2598409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598409).length < 2 ^ (prefixWord ++ tailWord_2598409).sum := by decide
  have hdescent : baseEnd_2598409 < baseStart_2598409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598497 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2598497 : Nat := 118140960795 + 2598497 * 2 ^ 59
def prefixEnd_2598497 : Nat := 4983230072969 + 3 ^ 40 * 2598497 * 2
def baseEnd_2598497 : Nat := 889518626844150068158157

theorem tailTrace_2598497 : CollatzResearch.WordTrace tailWord_2598497 prefixEnd_2598497 889518626844150068158157 := by
  unfold tailWord_2598497
  simp only [CollatzResearch.WordTrace]
  refine ⟨94774971667096631800945745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63183314444731087867297163 94774971667096631800945745)
  ·
    refine ⟨71081228750322473850709309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94774971667096631800945745 71081228750322473850709309)
    ·
      refine ⟨26655460781370927694015991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71081228750322473850709309 26655460781370927694015991)
      ·
        refine ⟨39983191172056391541023987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26655460781370927694015991 39983191172056391541023987)
        ·
          refine ⟨59974786758084587311535981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39983191172056391541023987 59974786758084587311535981)
          ·
            refine ⟨22490545034281720241825993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59974786758084587311535981 22490545034281720241825993)
            ·
              refine ⟨16867908775711290181369495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22490545034281720241825993 16867908775711290181369495)
              ·
                refine ⟨25301863163566935272054243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16867908775711290181369495 25301863163566935272054243)
                ·
                  refine ⟨37952794745350402908081365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25301863163566935272054243 37952794745350402908081365)
                  ·
                    refine ⟨889518626844150068158157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37952794745350402908081365 889518626844150068158157)
                    ·
                      rfl

theorem cell22_2598497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2598497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598497 prefixEnd_2598497 := by exact prefixLift 2598497
  have htrace : WordTrace (prefixWord ++ tailWord_2598497) baseStart_2598497 baseEnd_2598497 := by
    simpa [prefixWord, tailWord_2598497, baseEnd_2598497] using wordTrace_append hprefix tailTrace_2598497
  have hstable : (prefixWord ++ tailWord_2598497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598497).length < 2 ^ (prefixWord ++ tailWord_2598497).sum := by decide
  have hdescent : baseEnd_2598497 < baseStart_2598497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598499 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 5]
def baseStart_2598499 : Nat := 118140960795 + 2598499 * 2 ^ 59
def prefixEnd_2598499 : Nat := 4983230072969 + 3 ^ 40 * 2598499 * 2
def baseEnd_2598499 : Nat := 296506437161674243202717

theorem tailTrace_2598499 : CollatzResearch.WordTrace tailWord_2598499 prefixEnd_2598499 296506437161674243202717 := by
  unfold tailWord_2598499
  simp only [CollatzResearch.WordTrace]
  refine ⟨94775044613089386142518551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63183363075392924095012367 94775044613089386142518551)
  ·
    refine ⟨142162566919634079213777827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94775044613089386142518551 142162566919634079213777827)
    ·
      refine ⟨213243850379451118820666741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142162566919634079213777827 213243850379451118820666741)
      ·
        refine ⟨19991610973073542389437507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213243850379451118820666741 19991610973073542389437507)
        ·
          refine ⟨29987416459610313584156261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19991610973073542389437507 29987416459610313584156261)
          ·
            refine ⟨5622640586176933797029299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29987416459610313584156261 5622640586176933797029299)
            ·
              refine ⟨8433960879265400695543949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622640586176933797029299 8433960879265400695543949)
              ·
                refine ⟨3162735329724525260828981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8433960879265400695543949 3162735329724525260828981)
                ·
                  refine ⟨296506437161674243202717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162735329724525260828981 296506437161674243202717)
                  ·
                    rfl

theorem cell22_2598499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 5].length) (baseStart_2598499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598499 prefixEnd_2598499 := by exact prefixLift 2598499
  have htrace : WordTrace (prefixWord ++ tailWord_2598499) baseStart_2598499 baseEnd_2598499 := by
    simpa [prefixWord, tailWord_2598499, baseEnd_2598499] using wordTrace_append hprefix tailTrace_2598499
  have hstable : (prefixWord ++ tailWord_2598499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598499).length < 2 ^ (prefixWord ++ tailWord_2598499).sum := by decide
  have hdescent : baseEnd_2598499 < baseStart_2598499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598587 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_2598587 : Nat := 118140960795 + 2598587 * 2 ^ 59
def prefixEnd_2598587 : Nat := 4983230072969 + 3 ^ 40 * 2598587 * 2
def baseEnd_2598587 : Nat := 889549435683419833407881

theorem tailTrace_2598587 : CollatzResearch.WordTrace tailWord_2598587 prefixEnd_2598587 889549435683419833407881 := by
  unfold tailWord_2598587
  simp only [CollatzResearch.WordTrace]
  refine ⟨94778254236770577171722015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63185502824513718114481343 94778254236770577171722015)
  ·
    refine ⟨142167381355155865757583023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94778254236770577171722015 142167381355155865757583023)
    ·
      refine ⟨213251072032733798636374535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142167381355155865757583023 213251072032733798636374535)
      ·
        refine ⟨319876608049100697954561803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213251072032733798636374535 319876608049100697954561803)
        ·
          refine ⟨479814912073651046931842705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319876608049100697954561803 479814912073651046931842705)
          ·
            refine ⟨359861184055238285198882029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479814912073651046931842705 359861184055238285198882029)
            ·
              refine ⟨134947944020714356949580761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359861184055238285198882029 134947944020714356949580761)
              ·
                refine ⟨101210958015535767712185571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134947944020714356949580761 101210958015535767712185571)
                ·
                  refine ⟨151816437023303651568278357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101210958015535767712185571 151816437023303651568278357)
                  ·
                    refine ⟨889549435683419833407881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151816437023303651568278357 889549435683419833407881)
                    ·
                      rfl

theorem cell22_2598587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_2598587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598587 prefixEnd_2598587 := by exact prefixLift 2598587
  have htrace : WordTrace (prefixWord ++ tailWord_2598587) baseStart_2598587 baseEnd_2598587 := by
    simpa [prefixWord, tailWord_2598587, baseEnd_2598587] using wordTrace_append hprefix tailTrace_2598587
  have hstable : (prefixWord ++ tailWord_2598587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598587).length < 2 ^ (prefixWord ++ tailWord_2598587).sum := by decide
  have hdescent : baseEnd_2598587 < baseStart_2598587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598610 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_2598610 : Nat := 118140960795 + 2598610 * 2 ^ 59
def prefixEnd_2598610 : Nat := 4983230072969 + 3 ^ 40 * 2598610 * 2
def baseEnd_2598610 : Nat := 889557309053455440082811

theorem tailTrace_2598610 : CollatzResearch.WordTrace tailWord_2598610 prefixEnd_2598610 889557309053455440082811 := by
  unfold tailWord_2598610
  simp only [CollatzResearch.WordTrace]
  refine ⟨23694773278921813024952321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63186062077124834733206189 23694773278921813024952321)
  ·
    refine ⟨17771079959191359768714241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23694773278921813024952321 17771079959191359768714241)
    ·
      refine ⟨13328309969393519826535681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17771079959191359768714241 13328309969393519826535681)
      ·
        refine ⟨9996232477045139869901761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13328309969393519826535681 9996232477045139869901761)
        ·
          refine ⟨7497174357783854902426321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996232477045139869901761 7497174357783854902426321)
          ·
            refine ⟨5622880768337891176819741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7497174357783854902426321 5622880768337891176819741)
            ·
              refine ⟨2108580288126709191307403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5622880768337891176819741 2108580288126709191307403)
              ·
                refine ⟨3162870432190063786961105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108580288126709191307403 3162870432190063786961105)
                ·
                  refine ⟨2372152824142547840220829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162870432190063786961105 2372152824142547840220829)
                  ·
                    refine ⟨889557309053455440082811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372152824142547840220829 889557309053455440082811)
                    ·
                      rfl

theorem cell22_2598610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_2598610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598610 prefixEnd_2598610 := by exact prefixLift 2598610
  have htrace : WordTrace (prefixWord ++ tailWord_2598610) baseStart_2598610 baseEnd_2598610 := by
    simpa [prefixWord, tailWord_2598610, baseEnd_2598610] using wordTrace_append hprefix tailTrace_2598610
  have hstable : (prefixWord ++ tailWord_2598610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598610).length < 2 ^ (prefixWord ++ tailWord_2598610).sum := by decide
  have hdescent : baseEnd_2598610 < baseStart_2598610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598634 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_2598634 : Nat := 118140960795 + 2598634 * 2 ^ 59
def prefixEnd_2598634 : Nat := 4983230072969 + 3 ^ 40 * 2598634 * 2
def baseEnd_2598634 : Nat := 296521841581309125827579

theorem tailTrace_2598634 : CollatzResearch.WordTrace tailWord_2598634 prefixEnd_2598634 296521841581309125827579 := by
  unfold tailWord_2598634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23694992116900076049670739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63186645645066869465788637 23694992116900076049670739)
  ·
    refine ⟨35542488175350114074506109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23694992116900076049670739 35542488175350114074506109)
    ·
      refine ⟨13328433065756292777939791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35542488175350114074506109 13328433065756292777939791)
      ·
        refine ⟨19992649598634439166909687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13328433065756292777939791 19992649598634439166909687)
        ·
          refine ⟨29988974397951658750364531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19992649598634439166909687 29988974397951658750364531)
          ·
            refine ⟨44983461596927488125546797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29988974397951658750364531 44983461596927488125546797)
            ·
              refine ⟨16868798098847808047080049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44983461596927488125546797 16868798098847808047080049)
              ·
                refine ⟨12651598574135856035310037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16868798098847808047080049 12651598574135856035310037)
                ·
                  refine ⟨296521841581309125827579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12651598574135856035310037 296521841581309125827579)
                  ·
                    rfl

theorem cell22_2598634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_2598634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598634 prefixEnd_2598634 := by exact prefixLift 2598634
  have htrace : WordTrace (prefixWord ++ tailWord_2598634) baseStart_2598634 baseEnd_2598634 := by
    simpa [prefixWord, tailWord_2598634, baseEnd_2598634] using wordTrace_append hprefix tailTrace_2598634
  have hstable : (prefixWord ++ tailWord_2598634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598634).length < 2 ^ (prefixWord ++ tailWord_2598634).sum := by decide
  have hdescent : baseEnd_2598634 < baseStart_2598634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598728 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_2598728 : Nat := 118140960795 + 2598728 * 2 ^ 59
def prefixEnd_2598728 : Nat := 4983230072969 + 3 ^ 40 * 2598728 * 2
def baseEnd_2598728 : Nat := 889597702864942465632449

theorem tailTrace_2598728 : CollatzResearch.WordTrace tailWord_2598728 prefixEnd_2598728 889597702864942465632449 := by
  unfold tailWord_2598728
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391698464629879126302419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63188931286173172168403225 47391698464629879126302419)
  ·
    refine ⟨71087547696944818689453629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47391698464629879126302419 71087547696944818689453629)
    ·
      refine ⟨26657830386354307008545111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71087547696944818689453629 26657830386354307008545111)
      ·
        refine ⟨39986745579531460512817667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26657830386354307008545111 39986745579531460512817667)
        ·
          refine ⟨59980118369297190769226501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39986745579531460512817667 59980118369297190769226501)
          ·
            refine ⟨11246272194243223269229969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59980118369297190769226501 11246272194243223269229969)
            ·
              refine ⟨8434704145682417451922477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11246272194243223269229969 8434704145682417451922477)
              ·
                refine ⟨3163014054630906544470929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8434704145682417451922477 3163014054630906544470929)
                ·
                  refine ⟨2372260540973179908353197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163014054630906544470929 2372260540973179908353197)
                  ·
                    refine ⟨889597702864942465632449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372260540973179908353197 889597702864942465632449)
                    ·
                      rfl

theorem cell22_2598728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_2598728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598728 prefixEnd_2598728 := by exact prefixLift 2598728
  have htrace : WordTrace (prefixWord ++ tailWord_2598728) baseStart_2598728 baseEnd_2598728 := by
    simpa [prefixWord, tailWord_2598728, baseEnd_2598728] using wordTrace_append hprefix tailTrace_2598728
  have hstable : (prefixWord ++ tailWord_2598728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598728).length < 2 ^ (prefixWord ++ tailWord_2598728).sum := by decide
  have hdescent : baseEnd_2598728 < baseStart_2598728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598807 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 1, 3]
def baseStart_2598807 : Nat := 118140960795 + 2598807 * 2 ^ 59
def prefixEnd_2598807 : Nat := 4983230072969 + 3 ^ 40 * 2598807 * 2
def baseEnd_2598807 : Nat := 889624746179412592907207

theorem tailTrace_2598807 : CollatzResearch.WordTrace tailWord_2598807 prefixEnd_2598807 889624746179412592907207 := by
  unfold tailWord_2598807
  simp only [CollatzResearch.WordTrace]
  refine ⟨94786278295973554744730675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63190852197315703163153783 94786278295973554744730675)
  ·
    refine ⟨142179417443960332117096013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94786278295973554744730675 142179417443960332117096013)
    ·
      refine ⟨53317281541485124543911005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142179417443960332117096013 53317281541485124543911005)
      ·
        refine ⟨19993980578056921703966627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53317281541485124543911005 19993980578056921703966627)
        ·
          refine ⟨29990970867085382555949941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19993980578056921703966627 29990970867085382555949941)
          ·
            refine ⟨2811653518789254614620307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29990970867085382555949941 2811653518789254614620307)
            ·
              refine ⟨4217480278183881921930461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811653518789254614620307 4217480278183881921930461)
              ·
                refine ⟨1581555104318955720723923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4217480278183881921930461 1581555104318955720723923)
                ·
                  refine ⟨2372332656478433581085885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581555104318955720723923 2372332656478433581085885)
                  ·
                    refine ⟨889624746179412592907207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372332656478433581085885 889624746179412592907207)
                    ·
                      rfl

theorem cell22_2598807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_2598807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598807 prefixEnd_2598807 := by exact prefixLift 2598807
  have htrace : WordTrace (prefixWord ++ tailWord_2598807) baseStart_2598807 baseEnd_2598807 := by
    simpa [prefixWord, tailWord_2598807, baseEnd_2598807] using wordTrace_append hprefix tailTrace_2598807
  have hstable : (prefixWord ++ tailWord_2598807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598807).length < 2 ^ (prefixWord ++ tailWord_2598807).sum := by decide
  have hdescent : baseEnd_2598807 < baseStart_2598807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598816 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_2598816 : Nat := 118140960795 + 2598816 * 2 ^ 59
def prefixEnd_2598816 : Nat := 4983230072969 + 3 ^ 40 * 2598816 * 2
def baseEnd_2598816 : Nat := 889627827063339569432179

theorem tailTrace_2598816 : CollatzResearch.WordTrace tailWord_2598816 prefixEnd_2598816 889627827063339569432179 := by
  unfold tailWord_2598816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47393303276470474640904151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63191071035293966187872201 47393303276470474640904151)
  ·
    refine ⟨71089954914705711961356227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47393303276470474640904151 71089954914705711961356227)
    ·
      refine ⟨106634932372058567942034341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71089954914705711961356227 106634932372058567942034341)
      ·
        refine ⟨19994049819760981489131439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106634932372058567942034341 19994049819760981489131439)
        ·
          refine ⟨29991074729641472233697159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19994049819760981489131439 29991074729641472233697159)
          ·
            refine ⟨44986612094462208350545739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29991074729641472233697159 44986612094462208350545739)
            ·
              refine ⟨67479918141693312525818609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44986612094462208350545739 67479918141693312525818609)
              ·
                refine ⟨50609938606269984394363957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67479918141693312525818609 50609938606269984394363957)
                ·
                  refine ⟨4744681744337811036971621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50609938606269984394363957 4744681744337811036971621)
                  ·
                    refine ⟨889627827063339569432179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744681744337811036971621 889627827063339569432179)
                    ·
                      rfl

theorem cell22_2598816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_2598816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598816 prefixEnd_2598816 := by exact prefixLift 2598816
  have htrace : WordTrace (prefixWord ++ tailWord_2598816) baseStart_2598816 baseEnd_2598816 := by
    simpa [prefixWord, tailWord_2598816, baseEnd_2598816] using wordTrace_append hprefix tailTrace_2598816
  have hstable : (prefixWord ++ tailWord_2598816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598816).length < 2 ^ (prefixWord ++ tailWord_2598816).sum := by decide
  have hdescent : baseEnd_2598816 < baseStart_2598816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598824 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2598824 : Nat := 118140960795 + 2598824 * 2 ^ 59
def prefixEnd_2598824 : Nat := 4983230072969 + 3 ^ 40 * 2598824 * 2
def baseEnd_2598824 : Nat := 889630565626830215232155

theorem tailTrace_2598824 : CollatzResearch.WordTrace tailWord_2598824 prefixEnd_2598824 889630565626830215232155 := by
  unfold tailWord_2598824
  simp only [CollatzResearch.WordTrace]
  refine ⟨47393449168455983324049763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63191265557941311098733017 47393449168455983324049763)
  ·
    refine ⟨71090173752683974986074645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47393449168455983324049763 71090173752683974986074645)
    ·
      refine ⟨3332351894657061327472249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71090173752683974986074645 3332351894657061327472249)
      ·
        refine ⟨2499263920992795995604187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3332351894657061327472249 2499263920992795995604187)
        ·
          refine ⟨3748895881489193993406281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499263920992795995604187 3748895881489193993406281)
          ·
            refine ⟨2811671911116895495054711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3748895881489193993406281 2811671911116895495054711)
            ·
              refine ⟨4217507866675343242582067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811671911116895495054711 4217507866675343242582067)
              ·
                refine ⟨6326261800013014863873101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217507866675343242582067 6326261800013014863873101)
                ·
                  refine ⟨2372348175004880573952413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6326261800013014863873101 2372348175004880573952413)
                  ·
                    refine ⟨889630565626830215232155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372348175004880573952413 889630565626830215232155)
                    ·
                      rfl

theorem cell22_2598824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2598824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598824 prefixEnd_2598824 := by exact prefixLift 2598824
  have htrace : WordTrace (prefixWord ++ tailWord_2598824) baseStart_2598824 baseEnd_2598824 := by
    simpa [prefixWord, tailWord_2598824, baseEnd_2598824] using wordTrace_append hprefix tailTrace_2598824
  have hstable : (prefixWord ++ tailWord_2598824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598824).length < 2 ^ (prefixWord ++ tailWord_2598824).sum := by decide
  have hdescent : baseEnd_2598824 < baseStart_2598824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598938 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_2598938 : Nat := 118140960795 + 2598938 * 2 ^ 59
def prefixEnd_2598938 : Nat := 4983230072969 + 3 ^ 40 * 2598938 * 2
def baseEnd_2598938 : Nat := 296556530052190639293935

theorem tailTrace_2598938 : CollatzResearch.WordTrace tailWord_2598938 prefixEnd_2598938 296556530052190639293935 := by
  unfold tailWord_2598938
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697764064624741029437367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63194037505665976078499645 23697764064624741029437367)
  ·
    refine ⟨35546646096937111544156051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23697764064624741029437367 35546646096937111544156051)
    ·
      refine ⟨53319969145405667316234077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35546646096937111544156051 53319969145405667316234077)
      ·
        refine ⟨19994988429527125243587779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53319969145405667316234077 19994988429527125243587779)
        ·
          refine ⟨29992482644290687865381669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19994988429527125243587779 29992482644290687865381669)
          ·
            refine ⟨5623590495804503974759063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29992482644290687865381669 5623590495804503974759063)
            ·
              refine ⟨8435385743706755962138595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623590495804503974759063 8435385743706755962138595)
              ·
                refine ⟨12653078615560133943207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8435385743706755962138595 12653078615560133943207893)
                ·
                  refine ⟨296556530052190639293935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12653078615560133943207893 296556530052190639293935)
                  ·
                    rfl

theorem cell22_2598938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_2598938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2598938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2598938 prefixEnd_2598938 := by exact prefixLift 2598938
  have htrace : WordTrace (prefixWord ++ tailWord_2598938) baseStart_2598938 baseEnd_2598938 := by
    simpa [prefixWord, tailWord_2598938, baseEnd_2598938] using wordTrace_append hprefix tailTrace_2598938
  have hstable : (prefixWord ++ tailWord_2598938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598938).length < 2 ^ (prefixWord ++ tailWord_2598938).sum := by decide
  have hdescent : baseEnd_2598938 < baseStart_2598938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599000 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 6]
def baseStart_2599000 : Nat := 118140960795 + 2599000 * 2 ^ 59
def prefixEnd_2599000 : Nat := 4983230072969 + 3 ^ 40 * 2599000 * 2
def baseEnd_2599000 : Nat := 296563604674541474277205

theorem tailTrace_2599000 : CollatzResearch.WordTrace tailWord_2599000 prefixEnd_2599000 296563604674541474277205 := by
  unfold tailWord_2599000
  simp only [CollatzResearch.WordTrace]
  refine ⟨47396658792137174353253227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63195545056182899137670969 47396658792137174353253227)
  ·
    refine ⟨71094988188205761529879841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47396658792137174353253227 71094988188205761529879841)
    ·
      refine ⟨53321241141154321147409881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71094988188205761529879841 53321241141154321147409881)
      ·
        refine ⟨39990930855865740860557411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53321241141154321147409881 39990930855865740860557411)
        ·
          refine ⟨59986396283798611290836117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39990930855865740860557411 59986396283798611290836117)
          ·
            refine ⟨2811862325803059904257943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59986396283798611290836117 2811862325803059904257943)
            ·
              refine ⟨4217793488704589856386915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811862325803059904257943 4217793488704589856386915)
              ·
                refine ⟨6326690233056884784580373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217793488704589856386915 6326690233056884784580373)
                ·
                  refine ⟨296563604674541474277205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6326690233056884784580373 296563604674541474277205)
                  ·
                    rfl

theorem cell22_2599000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_2599000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599000 prefixEnd_2599000 := by exact prefixLift 2599000
  have htrace : WordTrace (prefixWord ++ tailWord_2599000) baseStart_2599000 baseEnd_2599000 := by
    simpa [prefixWord, tailWord_2599000, baseEnd_2599000] using wordTrace_append hprefix tailTrace_2599000
  have hstable : (prefixWord ++ tailWord_2599000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599000).length < 2 ^ (prefixWord ++ tailWord_2599000).sum := by decide
  have hdescent : baseEnd_2599000 < baseStart_2599000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599088 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_2599088 : Nat := 118140960795 + 2599088 * 2 ^ 59
def prefixEnd_2599088 : Nat := 4983230072969 + 3 ^ 40 * 2599088 * 2
def baseEnd_2599088 : Nat := 889720938222021526631345

theorem tailTrace_2599088 : CollatzResearch.WordTrace tailWord_2599088 prefixEnd_2599088 889720938222021526631345 := by
  unfold tailWord_2599088
  simp only [CollatzResearch.WordTrace]
  refine ⟨47398263603977769867854959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63197684805303693157139945 47398263603977769867854959)
  ·
    refine ⟨71097395405966654801782439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47398263603977769867854959 71097395405966654801782439)
    ·
      refine ⟨106646093108949982202673659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71097395405966654801782439 106646093108949982202673659)
      ·
        refine ⟨159969139663424973304010489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106646093108949982202673659 159969139663424973304010489)
        ·
          refine ⟨119976854747568729978007867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159969139663424973304010489 119976854747568729978007867)
          ·
            refine ⟨179965282121353094967011801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119976854747568729978007867 179965282121353094967011801)
            ·
              refine ⟨134973961591014821225258851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179965282121353094967011801 134973961591014821225258851)
              ·
                refine ⟨202460942386522231837888277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134973961591014821225258851 202460942386522231837888277)
                ·
                  refine ⟨9490356674368229617401013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 202460942386522231837888277 9490356674368229617401013)
                  ·
                    refine ⟨889720938222021526631345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9490356674368229617401013 889720938222021526631345)
                    ·
                      rfl

theorem cell22_2599088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_2599088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599088 prefixEnd_2599088 := by exact prefixLift 2599088
  have htrace : WordTrace (prefixWord ++ tailWord_2599088) baseStart_2599088 baseEnd_2599088 := by
    simpa [prefixWord, tailWord_2599088, baseEnd_2599088] using wordTrace_append hprefix tailTrace_2599088
  have hstable : (prefixWord ++ tailWord_2599088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599088).length < 2 ^ (prefixWord ++ tailWord_2599088).sum := by decide
  have hdescent : baseEnd_2599088 < baseStart_2599088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599137 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2599137 : Nat := 118140960795 + 2599137 * 2 ^ 59
def prefixEnd_2599137 : Nat := 4983230072969 + 3 ^ 40 * 2599137 * 2
def baseEnd_2599137 : Nat := 889737711923401732156195

theorem tailTrace_2599137 : CollatzResearch.WordTrace tailWord_2599137 prefixEnd_2599137 889737711923401732156195 := by
  unfold tailWord_2599137
  simp only [CollatzResearch.WordTrace]
  refine ⟨94798314384778021104243665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63198876256518680736162443 94798314384778021104243665)
  ·
    refine ⟨71098735788583515828182749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94798314384778021104243665 71098735788583515828182749)
    ·
      refine ⟨26662025920718818435568531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71098735788583515828182749 26662025920718818435568531)
      ·
        refine ⟨39993038881078227653352797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26662025920718818435568531 39993038881078227653352797)
        ·
          refine ⟨14997389580404335370007299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39993038881078227653352797 14997389580404335370007299)
          ·
            refine ⟨22496084370606503055010949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14997389580404335370007299 22496084370606503055010949)
            ·
              refine ⟨4218015819488719322814553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22496084370606503055010949 4218015819488719322814553)
              ·
                refine ⟨3163511864616539492110915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4218015819488719322814553 3163511864616539492110915)
                ·
                  refine ⟨4745267796924809238166373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163511864616539492110915 4745267796924809238166373)
                  ·
                    refine ⟨889737711923401732156195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4745267796924809238166373 889737711923401732156195)
                    ·
                      rfl

theorem cell22_2599137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2599137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599137 prefixEnd_2599137 := by exact prefixLift 2599137
  have htrace : WordTrace (prefixWord ++ tailWord_2599137) baseStart_2599137 baseEnd_2599137 := by
    simpa [prefixWord, tailWord_2599137, baseEnd_2599137] using wordTrace_append hprefix tailTrace_2599137
  have hstable : (prefixWord ++ tailWord_2599137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599137).length < 2 ^ (prefixWord ++ tailWord_2599137).sum := by decide
  have hdescent : baseEnd_2599137 < baseStart_2599137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599150 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2599150 : Nat := 118140960795 + 2599150 * 2 ^ 59
def prefixEnd_2599150 : Nat := 4983230072969 + 3 ^ 40 * 2599150 * 2
def baseEnd_2599150 : Nat := 889742162089074031581155

theorem tailTrace_2599150 : CollatzResearch.WordTrace tailWord_2599150 prefixEnd_2599150 889742162089074031581155 := by
  unfold tailWord_2599150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849848566716365540558363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63199192355820616216311269 11849848566716365540558363)
  ·
    refine ⟨17774772850074548310837545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11849848566716365540558363 17774772850074548310837545)
    ·
      refine ⟨13331079637555911233128159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17774772850074548310837545 13331079637555911233128159)
      ·
        refine ⟨19996619456333866849692239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331079637555911233128159 19996619456333866849692239)
        ·
          refine ⟨29994929184500800274538359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19996619456333866849692239 29994929184500800274538359)
          ·
            refine ⟨44992393776751200411807539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29994929184500800274538359 44992393776751200411807539)
            ·
              refine ⟨67488590665126800617711309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44992393776751200411807539 67488590665126800617711309)
              ·
                refine ⟨25308221499422550231641741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67488590665126800617711309 25308221499422550231641741)
                ·
                  refine ⟨9490583062283456336865653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25308221499422550231641741 9490583062283456336865653)
                  ·
                    refine ⟨889742162089074031581155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9490583062283456336865653 889742162089074031581155)
                    ·
                      rfl

theorem cell22_2599150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2599150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599150 prefixEnd_2599150 := by exact prefixLift 2599150
  have htrace : WordTrace (prefixWord ++ tailWord_2599150) baseStart_2599150 baseEnd_2599150 := by
    simpa [prefixWord, tailWord_2599150, baseEnd_2599150] using wordTrace_append hprefix tailTrace_2599150
  have hstable : (prefixWord ++ tailWord_2599150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599150).length < 2 ^ (prefixWord ++ tailWord_2599150).sum := by decide
  have hdescent : baseEnd_2599150 < baseStart_2599150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599167 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 2, 3]
def baseStart_2599167 : Nat := 118140960795 + 2599167 * 2 ^ 59
def prefixEnd_2599167 : Nat := 4983230072969 + 3 ^ 40 * 2599167 * 2
def baseEnd_2599167 : Nat := 889747981536491653906103

theorem tailTrace_2599167 : CollatzResearch.WordTrace tailWord_2599167 prefixEnd_2599167 889747981536491653906103 := by
  unfold tailWord_2599167
  simp only [CollatzResearch.WordTrace]
  refine ⟨94799408574669336227835755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63199605716446224151890503 94799408574669336227835755)
  ·
    refine ⟨142199112862004004341753633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94799408574669336227835755 142199112862004004341753633)
    ·
      refine ⟨106649334646503003256315225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142199112862004004341753633 106649334646503003256315225)
      ·
        refine ⟨79987000984877252442236419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106649334646503003256315225 79987000984877252442236419)
        ·
          refine ⟨119980501477315878663354629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79987000984877252442236419 119980501477315878663354629)
          ·
            refine ⟨22496344026996727249378993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119980501477315878663354629 22496344026996727249378993)
            ·
              refine ⟨16872258020247545437034245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22496344026996727249378993 16872258020247545437034245)
              ·
                refine ⟨3163548378796414769443921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16872258020247545437034245 3163548378796414769443921)
                ·
                  refine ⟨2372661284097311077082941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163548378796414769443921 2372661284097311077082941)
                  ·
                    refine ⟨889747981536491653906103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372661284097311077082941 889747981536491653906103)
                    ·
                      rfl

theorem cell22_2599167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_2599167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599167 prefixEnd_2599167 := by exact prefixLift 2599167
  have htrace : WordTrace (prefixWord ++ tailWord_2599167) baseStart_2599167 baseEnd_2599167 := by
    simpa [prefixWord, tailWord_2599167, baseEnd_2599167] using wordTrace_append hprefix tailTrace_2599167
  have hstable : (prefixWord ++ tailWord_2599167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599167).length < 2 ^ (prefixWord ++ tailWord_2599167).sum := by decide
  have hdescent : baseEnd_2599167 < baseStart_2599167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599169 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 4]
def baseStart_2599169 : Nat := 118140960795 + 2599169 * 2 ^ 59
def prefixEnd_2599169 : Nat := 4983230072969 + 3 ^ 40 * 2599169 * 2
def baseEnd_2599169 : Nat := 296582888725788105118699

theorem tailTrace_2599169 : CollatzResearch.WordTrace tailWord_2599169 prefixEnd_2599169 296582888725788105118699 := by
  unfold tailWord_2599169
  simp only [CollatzResearch.WordTrace]
  refine ⟨94799481520662090569408561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63199654347108060379605707 94799481520662090569408561)
  ·
    refine ⟨71099611140496567927056421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94799481520662090569408561 71099611140496567927056421)
    ·
      refine ⟨13331177088843106486323079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71099611140496567927056421 13331177088843106486323079)
      ·
        refine ⟨19996765633264659729484619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331177088843106486323079 19996765633264659729484619)
        ·
          refine ⟨29995148449896989594226929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19996765633264659729484619 29995148449896989594226929)
          ·
            refine ⟨22496361337422742195670197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29995148449896989594226929 22496361337422742195670197)
            ·
              refine ⟨2109033875383382080844081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22496361337422742195670197 2109033875383382080844081)
              ·
                refine ⟨1581775406537536560633061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109033875383382080844081 1581775406537536560633061)
                ·
                  refine ⟨296582888725788105118699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581775406537536560633061 296582888725788105118699)
                  ·
                    rfl

theorem cell22_2599169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_2599169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599169 prefixEnd_2599169 := by exact prefixLift 2599169
  have htrace : WordTrace (prefixWord ++ tailWord_2599169) baseStart_2599169 baseEnd_2599169 := by
    simpa [prefixWord, tailWord_2599169, baseEnd_2599169] using wordTrace_append hprefix tailTrace_2599169
  have hstable : (prefixWord ++ tailWord_2599169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599169).length < 2 ^ (prefixWord ++ tailWord_2599169).sum := by decide
  have hdescent : baseEnd_2599169 < baseStart_2599169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599180 : List Nat := [2, 2, 1, 2, 2, 2, 4, 7]
def baseStart_2599180 : Nat := 118140960795 + 2599180 * 2 ^ 59
def prefixEnd_2599180 : Nat := 4983230072969 + 3 ^ 40 * 2599180 * 2
def baseEnd_2599180 : Nat := 98861381300240439259007

theorem tailTrace_2599180 : CollatzResearch.WordTrace tailWord_2599180 prefixEnd_2599180 98861381300240439259007 := by
  unfold tailWord_2599180
  simp only [CollatzResearch.WordTrace]
  refine ⟨47399941361811119724029497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63199921815748159632039329 47399941361811119724029497)
  ·
    refine ⟨35549956021358339793022123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47399941361811119724029497 35549956021358339793022123)
    ·
      refine ⟨53324934032037509689533185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35549956021358339793022123 53324934032037509689533185)
      ·
        refine ⟨39993700524028132267149889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53324934032037509689533185 39993700524028132267149889)
        ·
          refine ⟨29995275393021099200362417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39993700524028132267149889 29995275393021099200362417)
          ·
            refine ⟨22496456544765824400271813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29995275393021099200362417 22496456544765824400271813)
            ·
              refine ⟨4218085602143592075050965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22496456544765824400271813 4218085602143592075050965)
              ·
                refine ⟨98861381300240439259007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4218085602143592075050965 98861381300240439259007)
                ·
                  rfl

theorem cell22_2599180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_2599180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599180 prefixEnd_2599180 := by exact prefixLift 2599180
  have htrace : WordTrace (prefixWord ++ tailWord_2599180) baseStart_2599180 baseEnd_2599180 := by
    simpa [prefixWord, tailWord_2599180, baseEnd_2599180] using wordTrace_append hprefix tailTrace_2599180
  have hstable : (prefixWord ++ tailWord_2599180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599180).length < 2 ^ (prefixWord ++ tailWord_2599180).sum := by decide
  have hdescent : baseEnd_2599180 < baseStart_2599180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599214 : List Nat := [4, 1, 3, 3, 2, 9]
def baseStart_2599214 : Nat := 118140960795 + 2599214 * 2 ^ 59
def prefixEnd_2599214 : Nat := 4983230072969 + 3 ^ 40 * 2599214 * 2
def baseEnd_2599214 : Nat := 10984741612308632073839

theorem tailTrace_2599214 : CollatzResearch.WordTrace tailWord_2599214 prefixEnd_2599214 10984741612308632073839 := by
  unfold tailWord_2599214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11850140350687382906849587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63200748536999375503197797 11850140350687382906849587)
  ·
    refine ⟨17775210526031074360274381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11850140350687382906849587 17775210526031074360274381)
    ·
      refine ⟨6665703947261652885102893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17775210526031074360274381 6665703947261652885102893)
      ·
        refine ⟨2499638980223119831913585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6665703947261652885102893 2499638980223119831913585)
        ·
          refine ⟨1874729235167339873935189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2499638980223119831913585 1874729235167339873935189)
          ·
            refine ⟨10984741612308632073839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1874729235167339873935189 10984741612308632073839)
            ·
              rfl

theorem cell22_2599214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 9].length) (baseStart_2599214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599214 prefixEnd_2599214 := by exact prefixLift 2599214
  have htrace : WordTrace (prefixWord ++ tailWord_2599214) baseStart_2599214 baseEnd_2599214 := by
    simpa [prefixWord, tailWord_2599214, baseEnd_2599214] using wordTrace_append hprefix tailTrace_2599214
  have hstable : (prefixWord ++ tailWord_2599214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599214).length < 2 ^ (prefixWord ++ tailWord_2599214).sum := by decide
  have hdescent : baseEnd_2599214 < baseStart_2599214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599240 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_2599240 : Nat := 118140960795 + 2599240 * 2 ^ 59
def prefixEnd_2599240 : Nat := 4983230072969 + 3 ^ 40 * 2599240 * 2
def baseEnd_2599240 : Nat := 889772970928343796830879

theorem tailTrace_2599240 : CollatzResearch.WordTrace tailWord_2599240 prefixEnd_2599240 889772970928343796830879 := by
  unfold tailWord_2599240
  simp only [CollatzResearch.WordTrace]
  refine ⟨47401035551702434847621587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63201380735603246463495449 47401035551702434847621587)
  ·
    refine ⟨71101553327553652271432381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47401035551702434847621587 71101553327553652271432381)
    ·
      refine ⟨26663082497832619601787143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71101553327553652271432381 26663082497832619601787143)
      ·
        refine ⟨39994623746748929402680715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26663082497832619601787143 39994623746748929402680715)
        ·
          refine ⟨59991935620123394104021073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39994623746748929402680715 59991935620123394104021073)
          ·
            refine ⟨44993951715092545578015805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59991935620123394104021073 44993951715092545578015805)
            ·
              refine ⟨16872731893159704591755927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44993951715092545578015805 16872731893159704591755927)
              ·
                refine ⟨25309097839739556887633891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16872731893159704591755927 25309097839739556887633891)
                ·
                  refine ⟨37963646759609335331450837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25309097839739556887633891 37963646759609335331450837)
                  ·
                    refine ⟨889772970928343796830879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37963646759609335331450837 889772970928343796830879)
                    ·
                      rfl

theorem cell22_2599240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_2599240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599240 prefixEnd_2599240 := by exact prefixLift 2599240
  have htrace : WordTrace (prefixWord ++ tailWord_2599240) baseStart_2599240 baseEnd_2599240 := by
    simpa [prefixWord, tailWord_2599240, baseEnd_2599240] using wordTrace_append hprefix tailTrace_2599240
  have hstable : (prefixWord ++ tailWord_2599240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599240).length < 2 ^ (prefixWord ++ tailWord_2599240).sum := by decide
  have hdescent : baseEnd_2599240 < baseStart_2599240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599276 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 5]
def baseStart_2599276 : Nat := 118140960795 + 2599276 * 2 ^ 59
def prefixEnd_2599276 : Nat := 4983230072969 + 3 ^ 40 * 2599276 * 2
def baseEnd_2599276 : Nat := 296595098154683900976923

theorem tailTrace_2599276 : CollatzResearch.WordTrace tailWord_2599276 prefixEnd_2599276 296595098154683900976923 := by
  unfold tailWord_2599276
  simp only [CollatzResearch.WordTrace]
  refine ⟨47401692065637223921776841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63202256087516298562369121 47401692065637223921776841)
  ·
    refine ⟨35551269049227917941332631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47401692065637223921776841 35551269049227917941332631)
    ·
      refine ⟨53326903573841876911998947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35551269049227917941332631 53326903573841876911998947)
      ·
        refine ⟨79990355360762815367998421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53326903573841876911998947 79990355360762815367998421)
        ·
          refine ⟨1874773953767878485187463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 79990355360762815367998421 1874773953767878485187463)
          ·
            refine ⟨2812160930651817727781195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874773953767878485187463 2812160930651817727781195)
            ·
              refine ⟨4218241395977726591671793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812160930651817727781195 4218241395977726591671793)
              ·
                refine ⟨3163681046983294943753845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4218241395977726591671793 3163681046983294943753845)
                ·
                  refine ⟨296595098154683900976923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163681046983294943753845 296595098154683900976923)
                  ·
                    rfl

theorem cell22_2599276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_2599276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599276 prefixEnd_2599276 := by exact prefixLift 2599276
  have htrace : WordTrace (prefixWord ++ tailWord_2599276) baseStart_2599276 baseEnd_2599276 := by
    simpa [prefixWord, tailWord_2599276, baseEnd_2599276] using wordTrace_append hprefix tailTrace_2599276
  have hstable : (prefixWord ++ tailWord_2599276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599276).length < 2 ^ (prefixWord ++ tailWord_2599276).sum := by decide
  have hdescent : baseEnd_2599276 < baseStart_2599276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599317 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2599317 : Nat := 118140960795 + 2599317 * 2 ^ 59
def prefixEnd_2599317 : Nat := 4983230072969 + 3 ^ 40 * 2599317 * 2
def baseEnd_2599317 : Nat := 889799329601941262655643

theorem tailTrace_2599317 : CollatzResearch.WordTrace tailWord_2599317 prefixEnd_2599317 889799329601941262655643 := by
  unfold tailWord_2599317
  simp only [CollatzResearch.WordTrace]
  refine ⟨94804879524125911845796205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63203253016083941230530803 94804879524125911845796205)
  ·
    refine ⟨35551829821547216942173577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94804879524125911845796205 35551829821547216942173577)
    ·
      refine ⟨26663872366160412706630183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35551829821547216942173577 26663872366160412706630183)
      ·
        refine ⟨39995808549240619059945275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26663872366160412706630183 39995808549240619059945275)
        ·
          refine ⟨59993712823860928589917913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39995808549240619059945275 59993712823860928589917913)
          ·
            refine ⟨44995284617895696442438435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59993712823860928589917913 44995284617895696442438435)
            ·
              refine ⟨67492926926843544663657653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44995284617895696442438435 67492926926843544663657653)
              ·
                refine ⟨6327461899391582312217905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67492926926843544663657653 6327461899391582312217905)
                ·
                  refine ⟨4745596424543686734163429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327461899391582312217905 4745596424543686734163429)
                  ·
                    refine ⟨889799329601941262655643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4745596424543686734163429 889799329601941262655643)
                    ·
                      rfl

theorem cell22_2599317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2599317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599317 prefixEnd_2599317 := by exact prefixLift 2599317
  have htrace : WordTrace (prefixWord ++ tailWord_2599317) baseStart_2599317 baseEnd_2599317 := by
    simpa [prefixWord, tailWord_2599317, baseEnd_2599317] using wordTrace_append hprefix tailTrace_2599317
  have hstable : (prefixWord ++ tailWord_2599317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599317).length < 2 ^ (prefixWord ++ tailWord_2599317).sum := by decide
  have hdescent : baseEnd_2599317 < baseStart_2599317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599336 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2599336 : Nat := 118140960795 + 2599336 * 2 ^ 59
def prefixEnd_2599336 : Nat := 4983230072969 + 3 ^ 40 * 2599336 * 2
def baseEnd_2599336 : Nat := 889805833690231546430585

theorem tailTrace_2599336 : CollatzResearch.WordTrace tailWord_2599336 prefixEnd_2599336 889805833690231546430585 := by
  unfold tailWord_2599336
  simp only [CollatzResearch.WordTrace]
  refine ⟨47402786255528539045368931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63203715007371385393825241 47402786255528539045368931)
  ·
    refine ⟨71104179383292808568053397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47402786255528539045368931 71104179383292808568053397)
    ·
      refine ⟨3333008408591850401627503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71104179383292808568053397 3333008408591850401627503)
      ·
        refine ⟨4999512612887775602441255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333008408591850401627503 4999512612887775602441255)
        ·
          refine ⟨7499268919331663403661883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4999512612887775602441255 7499268919331663403661883)
          ·
            refine ⟨11248903378997495105492825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499268919331663403661883 11248903378997495105492825)
            ·
              refine ⟨8436677534248121329119619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11248903378997495105492825 8436677534248121329119619)
              ·
                refine ⟨12655016301372181993679429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8436677534248121329119619 12655016301372181993679429)
                ·
                  refine ⟨2372815556507284123814893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12655016301372181993679429 2372815556507284123814893)
                  ·
                    refine ⟨889805833690231546430585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372815556507284123814893 889805833690231546430585)
                    ·
                      rfl

theorem cell22_2599336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2599336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599336 prefixEnd_2599336 := by exact prefixLift 2599336
  have htrace : WordTrace (prefixWord ++ tailWord_2599336) baseStart_2599336 baseEnd_2599336 := by
    simpa [prefixWord, tailWord_2599336, baseEnd_2599336] using wordTrace_append hprefix tailTrace_2599336
  have hstable : (prefixWord ++ tailWord_2599336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599336).length < 2 ^ (prefixWord ++ tailWord_2599336).sum := by decide
  have hdescent : baseEnd_2599336 < baseStart_2599336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599349 : List Nat := [1, 3, 3, 2, 3, 1, 2, 7]
def baseStart_2599349 : Nat := 118140960795 + 2599349 * 2 ^ 59
def prefixEnd_2599349 : Nat := 4983230072969 + 3 ^ 40 * 2599349 * 2
def baseEnd_2599349 : Nat := 98867809317322649539505

theorem tailTrace_2599349 : CollatzResearch.WordTrace tailWord_2599349 prefixEnd_2599349 98867809317322649539505 := by
  unfold tailWord_2599349
  simp only [CollatzResearch.WordTrace]
  refine ⟨94806046660009981310961101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63204031106673320873974067 94806046660009981310961101)
  ·
    refine ⟨35552267497503742991610413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94806046660009981310961101 35552267497503742991610413)
    ·
      refine ⟨13332100311563903621853905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35552267497503742991610413 13332100311563903621853905)
      ·
        refine ⟨9999075233672927716390429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13332100311563903621853905 9999075233672927716390429)
        ·
          refine ⟨3749653212627347893646411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9999075233672927716390429 3749653212627347893646411)
          ·
            refine ⟨5624479818941021840469617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749653212627347893646411 5624479818941021840469617)
            ·
              refine ⟨4218359864205766380352213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5624479818941021840469617 4218359864205766380352213)
              ·
                refine ⟨98867809317322649539505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4218359864205766380352213 98867809317322649539505)
                ·
                  rfl

theorem cell22_2599349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 7].length) (baseStart_2599349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599349 prefixEnd_2599349 := by exact prefixLift 2599349
  have htrace : WordTrace (prefixWord ++ tailWord_2599349) baseStart_2599349 baseEnd_2599349 := by
    simpa [prefixWord, tailWord_2599349, baseEnd_2599349] using wordTrace_append hprefix tailTrace_2599349
  have hstable : (prefixWord ++ tailWord_2599349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599349).length < 2 ^ (prefixWord ++ tailWord_2599349).sum := by decide
  have hdescent : baseEnd_2599349 < baseStart_2599349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599353 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 2, 3]
def baseStart_2599353 : Nat := 118140960795 + 2599353 * 2 ^ 59
def prefixEnd_2599353 : Nat := 4983230072969 + 3 ^ 40 * 2599353 * 2
def baseEnd_2599353 : Nat := 889811653137649168755533

theorem tailTrace_2599353 : CollatzResearch.WordTrace tailWord_2599353 prefixEnd_2599353 889811653137649168755533 := by
  unfold tailWord_2599353
  simp only [CollatzResearch.WordTrace]
  refine ⟨94806192551995489994106713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63204128367996993329404475 94806192551995489994106713)
  ·
    refine ⟨71104644413996617495580035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94806192551995489994106713 71104644413996617495580035)
    ·
      refine ⟨106656966620994926243370053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71104644413996617495580035 106656966620994926243370053)
      ·
        refine ⟨19998181241436548670631885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106656966620994926243370053 19998181241436548670631885)
        ·
          refine ⟨7499317965538705751486957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19998181241436548670631885 7499317965538705751486957)
          ·
            refine ⟨2812244237077014656807609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7499317965538705751486957 2812244237077014656807609)
            ·
              refine ⟨2109183177807760992605707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812244237077014656807609 2109183177807760992605707)
              ·
                refine ⟨3163774766711641488908561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109183177807760992605707 3163774766711641488908561)
                ·
                  refine ⟨2372831075033731116681421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163774766711641488908561 2372831075033731116681421)
                  ·
                    refine ⟨889811653137649168755533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372831075033731116681421 889811653137649168755533)
                    ·
                      rfl

theorem cell22_2599353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_2599353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599353 prefixEnd_2599353 := by exact prefixLift 2599353
  have htrace : WordTrace (prefixWord ++ tailWord_2599353) baseStart_2599353 baseEnd_2599353 := by
    simpa [prefixWord, tailWord_2599353, baseEnd_2599353] using wordTrace_append hprefix tailTrace_2599353
  have hstable : (prefixWord ++ tailWord_2599353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599353).length < 2 ^ (prefixWord ++ tailWord_2599353).sum := by decide
  have hdescent : baseEnd_2599353 < baseStart_2599353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599392 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_2599392 : Nat := 118140960795 + 2599392 * 2 ^ 59
def prefixEnd_2599392 : Nat := 4983230072969 + 3 ^ 40 * 2599392 * 2
def baseEnd_2599392 : Nat := 889825003634666067030413

theorem tailTrace_2599392 : CollatzResearch.WordTrace tailWord_2599392 prefixEnd_2599392 889825003634666067030413 := by
  unfold tailWord_2599392
  simp only [CollatzResearch.WordTrace]
  refine ⟨47403807499427099827388215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63205076665902799769850953 47403807499427099827388215)
  ·
    refine ⟨71105711249140649741082323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47403807499427099827388215 71105711249140649741082323)
    ·
      refine ⟨106658566873710974611623485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71105711249140649741082323 106658566873710974611623485)
      ·
        refine ⟨39996962577641615479358807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106658566873710974611623485 39996962577641615479358807)
        ·
          refine ⟨59995443866462423219038211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39996962577641615479358807 59995443866462423219038211)
          ·
            refine ⟨89993165799693634828557317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59995443866462423219038211 89993165799693634828557317)
            ·
              refine ⟨16873718587442556530354497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89993165799693634828557317 16873718587442556530354497)
              ·
                refine ⟨12655288940581917397765873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16873718587442556530354497 12655288940581917397765873)
                ·
                  refine ⟨9491466705436438048324405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12655288940581917397765873 9491466705436438048324405)
                  ·
                    refine ⟨889825003634666067030413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9491466705436438048324405 889825003634666067030413)
                    ·
                      rfl

theorem cell22_2599392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_2599392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599392 prefixEnd_2599392 := by exact prefixLift 2599392
  have htrace : WordTrace (prefixWord ++ tailWord_2599392) baseStart_2599392 baseEnd_2599392 := by
    simpa [prefixWord, tailWord_2599392, baseEnd_2599392] using wordTrace_append hprefix tailTrace_2599392
  have hstable : (prefixWord ++ tailWord_2599392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599392).length < 2 ^ (prefixWord ++ tailWord_2599392).sum := by decide
  have hdescent : baseEnd_2599392 < baseStart_2599392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599439 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 4]
def baseStart_2599439 : Nat := 118140960795 + 2599439 * 2 ^ 59
def prefixEnd_2599439 : Nat := 4983230072969 + 3 ^ 40 * 2599439 * 2
def baseEnd_2599439 : Nat := 296613697565057870368423

theorem tailTrace_2599439 : CollatzResearch.WordTrace tailWord_2599439 prefixEnd_2599439 296613697565057870368423 := by
  unfold tailWord_2599439
  simp only [CollatzResearch.WordTrace]
  refine ⟨94809329229683926681737371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63206219486455951121158247 94809329229683926681737371)
  ·
    refine ⟨142213993844525890022606057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94809329229683926681737371 142213993844525890022606057)
    ·
      refine ⟨106660495383394417516954543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142213993844525890022606057 106660495383394417516954543)
      ·
        refine ⟨159990743075091626275431815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106660495383394417516954543 159990743075091626275431815)
        ·
          refine ⟨239986114612637439413147723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159990743075091626275431815 239986114612637439413147723)
          ·
            refine ⟨359979171918956159119721585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239986114612637439413147723 359979171918956159119721585)
            ·
              refine ⟨269984378939217119339791189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359979171918956159119721585 269984378939217119339791189)
              ·
                refine ⟨1581939720346975308631589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 269984378939217119339791189 1581939720346975308631589)
                ·
                  refine ⟨296613697565057870368423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581939720346975308631589 296613697565057870368423)
                  ·
                    rfl

theorem cell22_2599439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 4].length) (baseStart_2599439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599439 prefixEnd_2599439 := by exact prefixLift 2599439
  have htrace : WordTrace (prefixWord ++ tailWord_2599439) baseStart_2599439 baseEnd_2599439 := by
    simpa [prefixWord, tailWord_2599439, baseEnd_2599439] using wordTrace_append hprefix tailTrace_2599439
  have hstable : (prefixWord ++ tailWord_2599439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599439).length < 2 ^ (prefixWord ++ tailWord_2599439).sum := by decide
  have hdescent : baseEnd_2599439 < baseStart_2599439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599456 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_2599456 : Nat := 118140960795 + 2599456 * 2 ^ 59
def prefixEnd_2599456 : Nat := 4983230072969 + 3 ^ 40 * 2599456 * 2
def baseEnd_2599456 : Nat := 296615637380863744476739

theorem tailTrace_2599456 : CollatzResearch.WordTrace tailWord_2599456 prefixEnd_2599456 296615637380863744476739 := by
  unfold tailWord_2599456
  simp only [CollatzResearch.WordTrace]
  refine ⟨47404974635311169292553111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63206632847081559056737481 47404974635311169292553111)
  ·
    refine ⟨71107461952966753938829667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47404974635311169292553111 71107461952966753938829667)
    ·
      refine ⟨106661192929450130908244501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71107461952966753938829667 106661192929450130908244501)
      ·
        refine ⟨4999743418567974886323961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106661192929450130908244501 4999743418567974886323961)
        ·
          refine ⟨3749807563925981164742971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4999743418567974886323961 3749807563925981164742971)
          ·
            refine ⟨5624711345888971747114457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749807563925981164742971 5624711345888971747114457)
            ·
              refine ⟨4218533509416728810335843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5624711345888971747114457 4218533509416728810335843)
              ·
                refine ⟨6327800264125093215503765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218533509416728810335843 6327800264125093215503765)
                ·
                  refine ⟨296615637380863744476739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6327800264125093215503765 296615637380863744476739)
                  ·
                    rfl

theorem cell22_2599456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_2599456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599456 prefixEnd_2599456 := by exact prefixLift 2599456
  have htrace : WordTrace (prefixWord ++ tailWord_2599456) baseStart_2599456 baseEnd_2599456 := by
    simpa [prefixWord, tailWord_2599456, baseEnd_2599456] using wordTrace_append hprefix tailTrace_2599456
  have hstable : (prefixWord ++ tailWord_2599456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599456).length < 2 ^ (prefixWord ++ tailWord_2599456).sum := by decide
  have hdescent : baseEnd_2599456 < baseStart_2599456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599484 : List Nat := [2, 2, 2, 2, 3, 2, 1, 8]
def baseStart_2599484 : Nat := 118140960795 + 2599484 * 2 ^ 59
def prefixEnd_2599484 : Nat := 4983230072969 + 3 ^ 40 * 2599484 * 2
def baseEnd_2599484 : Nat := 98872944123867610414459

theorem tailTrace_2599484 : CollatzResearch.WordTrace tailWord_2599484 prefixEnd_2599484 98872944123867610414459 := by
  unfold tailWord_2599484
  simp only [CollatzResearch.WordTrace]
  refine ⟨47405485257260449683562753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63207313676347266244750337 47405485257260449683562753)
  ·
    refine ⟨35554113942945337262672065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47405485257260449683562753 35554113942945337262672065)
    ·
      refine ⟨26665585457209002947004049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35554113942945337262672065 26665585457209002947004049)
      ·
        refine ⟨19999189092906752210253037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26665585457209002947004049 19999189092906752210253037)
        ·
          refine ⟨7499695909840032078844889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19999189092906752210253037 7499695909840032078844889)
          ·
            refine ⟨5624771932380024059133667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7499695909840032078844889 5624771932380024059133667)
            ·
              refine ⟨8437157898570036088700501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624771932380024059133667 8437157898570036088700501)
              ·
                refine ⟨98872944123867610414459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8437157898570036088700501 98872944123867610414459)
                ·
                  rfl

theorem cell22_2599484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_2599484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599484 prefixEnd_2599484 := by exact prefixLift 2599484
  have htrace : WordTrace (prefixWord ++ tailWord_2599484) baseStart_2599484 baseEnd_2599484 := by
    simpa [prefixWord, tailWord_2599484, baseEnd_2599484] using wordTrace_append hprefix tailTrace_2599484
  have hstable : (prefixWord ++ tailWord_2599484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599484).length < 2 ^ (prefixWord ++ tailWord_2599484).sum := by decide
  have hdescent : baseEnd_2599484 < baseStart_2599484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599497 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_2599497 : Nat := 118140960795 + 2599497 * 2 ^ 59
def prefixEnd_2599497 : Nat := 4983230072969 + 3 ^ 40 * 2599497 * 2
def baseEnd_2599497 : Nat := 889860947280480793155091

theorem tailTrace_2599497 : CollatzResearch.WordTrace tailWord_2599497 prefixEnd_2599497 889860947280480793155091 := by
  unfold tailWord_2599497
  simp only [CollatzResearch.WordTrace]
  refine ⟨94811444663473802587348745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63207629775649201724899163 94811444663473802587348745)
  ·
    refine ⟨71108583497605351940511559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94811444663473802587348745 71108583497605351940511559)
    ·
      refine ⟨106662875246408027910767339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71108583497605351940511559 106662875246408027910767339)
      ·
        refine ⟨159994312869612041866151009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106662875246408027910767339 159994312869612041866151009)
        ·
          refine ⟨119995734652209031399613257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159994312869612041866151009 119995734652209031399613257)
          ·
            refine ⟨89996800989156773549709943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119995734652209031399613257 89996800989156773549709943)
            ·
              refine ⟨134995201483735160324564915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89996800989156773549709943 134995201483735160324564915)
              ·
                refine ⟨202492802225602740486847373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134995201483735160324564915 202492802225602740486847373)
                ·
                  refine ⟨75934800834601027682567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202492802225602740486847373 75934800834601027682567765)
                  ·
                    refine ⟨889860947280480793155091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75934800834601027682567765 889860947280480793155091)
                    ·
                      rfl

theorem cell22_2599497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_2599497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599497 prefixEnd_2599497 := by exact prefixLift 2599497
  have htrace : WordTrace (prefixWord ++ tailWord_2599497) baseStart_2599497 baseEnd_2599497 := by
    simpa [prefixWord, tailWord_2599497, baseEnd_2599497] using wordTrace_append hprefix tailTrace_2599497
  have hstable : (prefixWord ++ tailWord_2599497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599497).length < 2 ^ (prefixWord ++ tailWord_2599497).sum := by decide
  have hdescent : baseEnd_2599497 < baseStart_2599497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599499 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 5, 3]
def baseStart_2599499 : Nat := 118140960795 + 2599499 * 2 ^ 59
def prefixEnd_2599499 : Nat := 4983230072969 + 3 ^ 40 * 2599499 * 2
def baseEnd_2599499 : Nat := 889861631921353454605085

theorem tailTrace_2599499 : CollatzResearch.WordTrace tailWord_2599499 prefixEnd_2599499 889861631921353454605085 := by
  unfold tailWord_2599499
  simp only [CollatzResearch.WordTrace]
  refine ⟨94811517609466556928921551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63207678406311037952614367 94811517609466556928921551)
  ·
    refine ⟨142217276414199835393382327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94811517609466556928921551 142217276414199835393382327)
    ·
      refine ⟨213325914621299753090073491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142217276414199835393382327 213325914621299753090073491)
      ·
        refine ⟨319988871931949629635110237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213325914621299753090073491 319988871931949629635110237)
        ·
          refine ⟨119995826974481111113166339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319988871931949629635110237 119995826974481111113166339)
          ·
            refine ⟨179993740461721666669749509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119995826974481111113166339 179993740461721666669749509)
            ·
              refine ⟨33748826336572812500578033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179993740461721666669749509 33748826336572812500578033)
              ·
                refine ⟨25311619752429609375433525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33748826336572812500578033 25311619752429609375433525)
                ·
                  refine ⟨2372964351790275878946893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25311619752429609375433525 2372964351790275878946893)
                  ·
                    refine ⟨889861631921353454605085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372964351790275878946893 889861631921353454605085)
                    ·
                      rfl

theorem cell22_2599499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 3].length) (baseStart_2599499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599499 prefixEnd_2599499 := by exact prefixLift 2599499
  have htrace : WordTrace (prefixWord ++ tailWord_2599499) baseStart_2599499 baseEnd_2599499 := by
    simpa [prefixWord, tailWord_2599499, baseEnd_2599499] using wordTrace_append hprefix tailTrace_2599499
  have hstable : (prefixWord ++ tailWord_2599499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599499).length < 2 ^ (prefixWord ++ tailWord_2599499).sum := by decide
  have hdescent : baseEnd_2599499 < baseStart_2599499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599501 : List Nat := [1, 6, 1, 1, 2, 3, 8]
def baseStart_2599501 : Nat := 118140960795 + 2599501 * 2 ^ 59
def prefixEnd_2599501 : Nat := 4983230072969 + 3 ^ 40 * 2599501 * 2
def baseEnd_2599501 : Nat := 32957863576378745039077

theorem tailTrace_2599501 : CollatzResearch.WordTrace tailWord_2599501 prefixEnd_2599501 32957863576378745039077 := by
  unfold tailWord_2599501
  simp only [CollatzResearch.WordTrace]
  refine ⟨94811590555459311270494357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63207727036972874180329571 94811590555459311270494357)
  ·
    refine ⟨4444293307287155215804423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94811590555459311270494357 4444293307287155215804423)
    ·
      refine ⟨6666439960930732823706635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444293307287155215804423 6666439960930732823706635)
      ·
        refine ⟨9999659941396099235559953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666439960930732823706635 9999659941396099235559953)
        ·
          refine ⟨7499744956047074426669965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9999659941396099235559953 7499744956047074426669965)
          ·
            refine ⟨2812404358517652910001237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7499744956047074426669965 2812404358517652910001237)
            ·
              refine ⟨32957863576378745039077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2812404358517652910001237 32957863576378745039077)
              ·
                rfl

theorem cell22_2599501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 8].length) (baseStart_2599501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599501 prefixEnd_2599501 := by exact prefixLift 2599501
  have htrace : WordTrace (prefixWord ++ tailWord_2599501) baseStart_2599501 baseEnd_2599501 := by
    simpa [prefixWord, tailWord_2599501, baseEnd_2599501] using wordTrace_append hprefix tailTrace_2599501
  have hstable : (prefixWord ++ tailWord_2599501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599501).length < 2 ^ (prefixWord ++ tailWord_2599501).sum := by decide
  have hdescent : baseEnd_2599501 < baseStart_2599501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599578 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_2599578 : Nat := 118140960795 + 2599578 * 2 ^ 59
def prefixEnd_2599578 : Nat := 4983230072969 + 3 ^ 40 * 2599578 * 2
def baseEnd_2599578 : Nat := 889888675235823581879843

theorem tailTrace_2599578 : CollatzResearch.WordTrace tailWord_2599578 prefixEnd_2599578 889888675235823581879843 := by
  unfold tailWord_2599578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23703599744045088355261847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63209599317453568947364925 23703599744045088355261847)
  ·
    refine ⟨35555399616067632532892771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23703599744045088355261847 35555399616067632532892771)
    ·
      refine ⟨53333099424101448799339157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35555399616067632532892771 53333099424101448799339157)
      ·
        refine ⟨2499989035504755412469023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53333099424101448799339157 2499989035504755412469023)
        ·
          refine ⟨3749983553257133118703535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499989035504755412469023 3749983553257133118703535)
          ·
            refine ⟨5624975329885699678055303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749983553257133118703535 5624975329885699678055303)
            ·
              refine ⟨8437462994828549517082955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624975329885699678055303 8437462994828549517082955)
              ·
                refine ⟨12656194492242824275624433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8437462994828549517082955 12656194492242824275624433)
                ·
                  refine ⟨9492145869182118206718325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12656194492242824275624433 9492145869182118206718325)
                  ·
                    refine ⟨889888675235823581879843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9492145869182118206718325 889888675235823581879843)
                    ·
                      rfl

theorem cell22_2599578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_2599578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599578 prefixEnd_2599578 := by exact prefixLift 2599578
  have htrace : WordTrace (prefixWord ++ tailWord_2599578) baseStart_2599578 baseEnd_2599578 := by
    simpa [prefixWord, tailWord_2599578, baseEnd_2599578] using wordTrace_append hprefix tailTrace_2599578
  have hstable : (prefixWord ++ tailWord_2599578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599578).length < 2 ^ (prefixWord ++ tailWord_2599578).sum := by decide
  have hdescent : baseEnd_2599578 < baseStart_2599578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599640 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 2, 3]
def baseStart_2599640 : Nat := 118140960795 + 2599640 * 2 ^ 59
def prefixEnd_2599640 : Nat := 4983230072969 + 3 ^ 40 * 2599640 * 2
def baseEnd_2599640 : Nat := 889909899102876086829653

theorem tailTrace_2599640 : CollatzResearch.WordTrace tailWord_2599640 prefixEnd_2599640 889909899102876086829653 := by
  unfold tailWord_2599640
  simp only [CollatzResearch.WordTrace]
  refine ⟨47408330150977869004902187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63211106867970492006536249 47408330150977869004902187)
  ·
    refine ⟨71112495226466803507353281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47408330150977869004902187 71112495226466803507353281)
    ·
      refine ⟨53334371419850102630514961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71112495226466803507353281 53334371419850102630514961)
      ·
        refine ⟨40000778564887576972886221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53334371419850102630514961 40000778564887576972886221)
        ·
          refine ⟨15000291961832841364832333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40000778564887576972886221 15000291961832841364832333)
          ·
            refine ⟨5625109485687315511812125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15000291961832841364832333 5625109485687315511812125)
            ·
              refine ⟨2109416057132743316929547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5625109485687315511812125 2109416057132743316929547)
              ·
                refine ⟨3164124085699114975394321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109416057132743316929547 3164124085699114975394321)
                ·
                  refine ⟨2373093064274336231545741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164124085699114975394321 2373093064274336231545741)
                  ·
                    refine ⟨889909899102876086829653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2373093064274336231545741 889909899102876086829653)
                    ·
                      rfl

theorem cell22_2599640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_2599640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599640 prefixEnd_2599640 := by exact prefixLift 2599640
  have htrace : WordTrace (prefixWord ++ tailWord_2599640) baseStart_2599640 baseEnd_2599640 := by
    simpa [prefixWord, tailWord_2599640, baseEnd_2599640] using wordTrace_append hprefix tailTrace_2599640
  have hstable : (prefixWord ++ tailWord_2599640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599640).length < 2 ^ (prefixWord ++ tailWord_2599640).sum := by decide
  have hdescent : baseEnd_2599640 < baseStart_2599640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599653 : List Nat := [1, 3, 1, 4, 1, 4, 2, 6]
def baseStart_2599653 : Nat := 118140960795 + 2599653 * 2 ^ 59
def prefixEnd_2599653 : Nat := 4983230072969 + 3 ^ 40 * 2599653 * 2
def baseEnd_2599653 : Nat := 98879372140949820694957

theorem tailTrace_2599653 : CollatzResearch.WordTrace tailWord_2599653 prefixEnd_2599653 98879372140949820694957 := by
  unfold tailWord_2599653
  simp only [CollatzResearch.WordTrace]
  refine ⟨94817134450908641230027613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63211422967272427486685075 94817134450908641230027613)
  ·
    refine ⟨35556425419090740461260355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94817134450908641230027613 35556425419090740461260355)
    ·
      refine ⟨53334638128636110691890533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35556425419090740461260355 53334638128636110691890533)
      ·
        refine ⟨10000244649119270754729475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53334638128636110691890533 10000244649119270754729475)
        ·
          refine ⟨15000366973678906132094213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10000244649119270754729475 15000366973678906132094213)
          ·
            refine ⟨2812568807564794899767665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15000366973678906132094213 2812568807564794899767665)
            ·
              refine ⟨2109426605673596174825749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812568807564794899767665 2109426605673596174825749)
              ·
                refine ⟨98879372140949820694957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2109426605673596174825749 98879372140949820694957)
                ·
                  rfl

theorem cell22_2599653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 6].length) (baseStart_2599653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599653 prefixEnd_2599653 := by exact prefixLift 2599653
  have htrace : WordTrace (prefixWord ++ tailWord_2599653) baseStart_2599653 baseEnd_2599653 := by
    simpa [prefixWord, tailWord_2599653, baseEnd_2599653] using wordTrace_append hprefix tailTrace_2599653
  have hstable : (prefixWord ++ tailWord_2599653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599653).length < 2 ^ (prefixWord ++ tailWord_2599653).sum := by decide
  have hdescent : baseEnd_2599653 < baseStart_2599653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599664 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_2599664 : Nat := 118140960795 + 2599664 * 2 ^ 59
def prefixEnd_2599664 : Nat := 4983230072969 + 3 ^ 40 * 2599664 * 2
def baseEnd_2599664 : Nat := 296639371597782674743193

theorem tailTrace_2599664 : CollatzResearch.WordTrace tailWord_2599664 prefixEnd_2599664 296639371597782674743193 := by
  unfold tailWord_2599664
  simp only [CollatzResearch.WordTrace]
  refine ⟨47408767826934395054339023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63211690435912526739118697 47408767826934395054339023)
  ·
    refine ⟨71113151740401592581508535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47408767826934395054339023 71113151740401592581508535)
    ·
      refine ⟨106669727610602388872262803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71113151740401592581508535 106669727610602388872262803)
      ·
        refine ⟨160004591415903583308394205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106669727610602388872262803 160004591415903583308394205)
        ·
          refine ⟨60001721780963843740647827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160004591415903583308394205 60001721780963843740647827)
          ·
            refine ⟨90002582671445765610971741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60001721780963843740647827 90002582671445765610971741)
            ·
              refine ⟨33750968501792162104114403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90002582671445765610971741 33750968501792162104114403)
              ·
                refine ⟨50626452752688243156171605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33750968501792162104114403 50626452752688243156171605)
                ·
                  refine ⟨296639371597782674743193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50626452752688243156171605 296639371597782674743193)
                  ·
                    rfl

theorem cell22_2599664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_2599664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599664 prefixEnd_2599664 := by exact prefixLift 2599664
  have htrace : WordTrace (prefixWord ++ tailWord_2599664) baseStart_2599664 baseEnd_2599664 := by
    simpa [prefixWord, tailWord_2599664, baseEnd_2599664] using wordTrace_append hprefix tailTrace_2599664
  have hstable : (prefixWord ++ tailWord_2599664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599664).length < 2 ^ (prefixWord ++ tailWord_2599664).sum := by decide
  have hdescent : baseEnd_2599664 < baseStart_2599664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599681 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 5]
def baseStart_2599681 : Nat := 118140960795 + 2599681 * 2 ^ 59
def prefixEnd_2599681 : Nat := 4983230072969 + 3 ^ 40 * 2599681 * 2
def baseEnd_2599681 : Nat := 296641311413588548851509

theorem tailTrace_2599681 : CollatzResearch.WordTrace tailWord_2599681 prefixEnd_2599681 296641311413588548851509 := by
  unfold tailWord_2599681
  simp only [CollatzResearch.WordTrace]
  refine ⟨94818155694807202012046897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63212103796538134674697931 94818155694807202012046897)
  ·
    refine ⟨71113616771105401509035173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94818155694807202012046897 71113616771105401509035173)
    ·
      refine ⟨13333803144582262782944095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71113616771105401509035173 13333803144582262782944095)
      ·
        refine ⟨20000704716873394174416143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13333803144582262782944095 20000704716873394174416143)
        ·
          refine ⟨30001057075310091261624215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20000704716873394174416143 30001057075310091261624215)
          ·
            refine ⟨45001585612965136892436323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30001057075310091261624215 45001585612965136892436323)
            ·
              refine ⟨67502378419447705338654485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45001585612965136892436323 67502378419447705338654485)
              ·
                refine ⟨3164173988411611187749429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67502378419447705338654485 3164173988411611187749429)
                ·
                  refine ⟨296641311413588548851509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3164173988411611187749429 296641311413588548851509)
                  ·
                    rfl

theorem cell22_2599681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_2599681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599681 prefixEnd_2599681 := by exact prefixLift 2599681
  have htrace : WordTrace (prefixWord ++ tailWord_2599681) baseStart_2599681 baseEnd_2599681 := by
    simpa [prefixWord, tailWord_2599681, baseEnd_2599681] using wordTrace_append hprefix tailTrace_2599681
  have hstable : (prefixWord ++ tailWord_2599681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599681).length < 2 ^ (prefixWord ++ tailWord_2599681).sum := by decide
  have hdescent : baseEnd_2599681 < baseStart_2599681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599803 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 3, 3]
def baseStart_2599803 : Nat := 118140960795 + 2599803 * 2 ^ 59
def prefixEnd_2599803 : Nat := 4983230072969 + 3 ^ 40 * 2599803 * 2
def baseEnd_2599803 : Nat := 889965697333997995004153

theorem tailTrace_2599803 : CollatzResearch.WordTrace tailWord_2599803 prefixEnd_2599803 889965697333997995004153 := by
  unfold tailWord_2599803
  simp only [CollatzResearch.WordTrace]
  refine ⟨94822605400365216847988063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63215070266910144565325375 94822605400365216847988063)
  ·
    refine ⟨142233908100547825271982095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94822605400365216847988063 142233908100547825271982095)
    ·
      refine ⟨213350862150821737907973143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142233908100547825271982095 213350862150821737907973143)
      ·
        refine ⟨320026293226232606861959715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213350862150821737907973143 320026293226232606861959715)
        ·
          refine ⟨480039439839348910292939573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320026293226232606861959715 480039439839348910292939573)
          ·
            refine ⟨45003697484938960339963085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 480039439839348910292939573 45003697484938960339963085)
            ·
              refine ⟨16876386556852110127486157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45003697484938960339963085 16876386556852110127486157)
              ·
                refine ⟨6328644958819541297807309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16876386556852110127486157 6328644958819541297807309)
                ·
                  refine ⟨2373241859557327986677741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6328644958819541297807309 2373241859557327986677741)
                  ·
                    refine ⟨889965697333997995004153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2373241859557327986677741 889965697333997995004153)
                    ·
                      rfl

theorem cell22_2599803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 3].length) (baseStart_2599803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599803 prefixEnd_2599803 := by exact prefixLift 2599803
  have htrace : WordTrace (prefixWord ++ tailWord_2599803) baseStart_2599803 baseEnd_2599803 := by
    simpa [prefixWord, tailWord_2599803, baseEnd_2599803] using wordTrace_append hprefix tailTrace_2599803
  have hstable : (prefixWord ++ tailWord_2599803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599803).length < 2 ^ (prefixWord ++ tailWord_2599803).sum := by decide
  have hdescent : baseEnd_2599803 < baseStart_2599803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599880 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_2599880 : Nat := 118140960795 + 2599880 * 2 ^ 59
def prefixEnd_2599880 : Nat := 4983230072969 + 3 ^ 40 * 2599880 * 2
def baseEnd_2599880 : Nat := 889992056007595460828917

theorem tailTrace_2599880 : CollatzResearch.WordTrace tailWord_2599880 prefixEnd_2599880 889992056007595460828917 := by
  unfold tailWord_2599880
  simp only [CollatzResearch.WordTrace]
  refine ⟨47412706910543129499270547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63216942547390839332360729 47412706910543129499270547)
  ·
    refine ⟨71119060365814694248905821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47412706910543129499270547 71119060365814694248905821)
    ·
      refine ⟨26669647637180510343339683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71119060365814694248905821 26669647637180510343339683)
      ·
        refine ⟨40004471455770765515009525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26669647637180510343339683 40004471455770765515009525)
        ·
          refine ⟨3750419198978509267032143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40004471455770765515009525 3750419198978509267032143)
          ·
            refine ⟨5625628798467763900548215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750419198978509267032143 5625628798467763900548215)
            ·
              refine ⟨8438443197701645850822323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625628798467763900548215 8438443197701645850822323)
              ·
                refine ⟨12657664796552468776233485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8438443197701645850822323 12657664796552468776233485)
                ·
                  refine ⟨4746624298707175791087557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12657664796552468776233485 4746624298707175791087557)
                  ·
                    refine ⟨889992056007595460828917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746624298707175791087557 889992056007595460828917)
                    ·
                      rfl

theorem cell22_2599880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_2599880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599880 prefixEnd_2599880 := by exact prefixLift 2599880
  have htrace : WordTrace (prefixWord ++ tailWord_2599880) baseStart_2599880 baseEnd_2599880 := by
    simpa [prefixWord, tailWord_2599880, baseEnd_2599880] using wordTrace_append hprefix tailTrace_2599880
  have hstable : (prefixWord ++ tailWord_2599880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599880).length < 2 ^ (prefixWord ++ tailWord_2599880).sum := by decide
  have hdescent : baseEnd_2599880 < baseStart_2599880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599897 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 1, 4]
def baseStart_2599897 : Nat := 118140960795 + 2599897 * 2 ^ 59
def prefixEnd_2599897 : Nat := 4983230072969 + 3 ^ 40 * 2599897 * 2
def baseEnd_2599897 : Nat := 889997875455013083153865

theorem tailTrace_2599897 : CollatzResearch.WordTrace tailWord_2599897 prefixEnd_2599897 889997875455013083153865 := by
  unfold tailWord_2599897
  simp only [CollatzResearch.WordTrace]
  refine ⟨94826033862024670901909945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63217355908016447267939963 94826033862024670901909945)
  ·
    refine ⟨71119525396518503176432459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94826033862024670901909945 71119525396518503176432459)
    ·
      refine ⟨106679288094777754764648689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71119525396518503176432459 106679288094777754764648689)
      ·
        refine ⟨80009466071083316073486517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106679288094777754764648689 80009466071083316073486517)
        ·
          refine ⟨7500887444164060881889361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80009466071083316073486517 7500887444164060881889361)
          ·
            refine ⟨5625665583123045661417021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7500887444164060881889361 5625665583123045661417021)
            ·
              refine ⟨2109624593671142123031383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5625665583123045661417021 2109624593671142123031383)
              ·
                refine ⟨3164436890506713184547075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109624593671142123031383 3164436890506713184547075)
                ·
                  refine ⟨4746655335760069776820613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164436890506713184547075 4746655335760069776820613)
                  ·
                    refine ⟨889997875455013083153865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746655335760069776820613 889997875455013083153865)
                    ·
                      rfl

theorem cell22_2599897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_2599897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599897 prefixEnd_2599897 := by exact prefixLift 2599897
  have htrace : WordTrace (prefixWord ++ tailWord_2599897) baseStart_2599897 baseEnd_2599897 := by
    simpa [prefixWord, tailWord_2599897, baseEnd_2599897] using wordTrace_append hprefix tailTrace_2599897
  have hstable : (prefixWord ++ tailWord_2599897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599897).length < 2 ^ (prefixWord ++ tailWord_2599897).sum := by decide
  have hdescent : baseEnd_2599897 < baseStart_2599897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599908 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2599908 : Nat := 118140960795 + 2599908 * 2 ^ 59
def prefixEnd_2599908 : Nat := 4983230072969 + 3 ^ 40 * 2599908 * 2
def baseEnd_2599908 : Nat := 890001640979812721128831

theorem tailTrace_2599908 : CollatzResearch.WordTrace tailWord_2599908 prefixEnd_2599908 890001640979812721128831 := by
  unfold tailWord_2599908
  simp only [CollatzResearch.WordTrace]
  refine ⟨47413217532492409890280189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63217623376656546520373585 47413217532492409890280189)
  ·
    refine ⟨17779956574684653708855071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47413217532492409890280189 17779956574684653708855071)
    ·
      refine ⟨26669934862026980563282607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17779956574684653708855071 26669934862026980563282607)
      ·
        refine ⟨40004902293040470844923911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26669934862026980563282607 40004902293040470844923911)
        ·
          refine ⟨60007353439560706267385867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40004902293040470844923911 60007353439560706267385867)
          ·
            refine ⟨90011030159341059401078801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60007353439560706267385867 90011030159341059401078801)
            ·
              refine ⟨67508272619505794550809101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90011030159341059401078801 67508272619505794550809101)
              ·
                refine ⟨25315602232314672956553413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67508272619505794550809101 25315602232314672956553413)
                ·
                  refine ⟨4746675418559001179353765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25315602232314672956553413 4746675418559001179353765)
                  ·
                    refine ⟨890001640979812721128831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746675418559001179353765 890001640979812721128831)
                    ·
                      rfl

theorem cell22_2599908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2599908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599908 prefixEnd_2599908 := by exact prefixLift 2599908
  have htrace : WordTrace (prefixWord ++ tailWord_2599908) baseStart_2599908 baseEnd_2599908 := by
    simpa [prefixWord, tailWord_2599908, baseEnd_2599908] using wordTrace_append hprefix tailTrace_2599908
  have hstable : (prefixWord ++ tailWord_2599908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599908).length < 2 ^ (prefixWord ++ tailWord_2599908).sum := by decide
  have hdescent : baseEnd_2599908 < baseStart_2599908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599912 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 4]
def baseStart_2599912 : Nat := 118140960795 + 2599912 * 2 ^ 59
def prefixEnd_2599912 : Nat := 4983230072969 + 3 ^ 40 * 2599912 * 2
def baseEnd_2599912 : Nat := 296667670087186014676273

theorem tailTrace_2599912 : CollatzResearch.WordTrace tailWord_2599912 prefixEnd_2599912 296667670087186014676273 := by
  unfold tailWord_2599912
  simp only [CollatzResearch.WordTrace]
  refine ⟨47413290478485164231852995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63217720637980218975803993 47413290478485164231852995)
  ·
    refine ⟨71119935717727746347779493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47413290478485164231852995 71119935717727746347779493)
    ·
      refine ⟨13334987947073952440208655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71119935717727746347779493 13334987947073952440208655)
      ·
        refine ⟨20002481920610928660312983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13334987947073952440208655 20002481920610928660312983)
        ·
          refine ⟨30003722880916392990469475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20002481920610928660312983 30003722880916392990469475)
          ·
            refine ⟨45005584321374589485704213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30003722880916392990469475 45005584321374589485704213)
            ·
              refine ⟨2109636765064433882142385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45005584321374589485704213 2109636765064433882142385)
              ·
                refine ⟨1582227573798325411606789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109636765064433882142385 1582227573798325411606789)
                ·
                  refine ⟨296667670087186014676273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1582227573798325411606789 296667670087186014676273)
                  ·
                    rfl

theorem cell22_2599912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_2599912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599912 prefixEnd_2599912 := by exact prefixLift 2599912
  have htrace : WordTrace (prefixWord ++ tailWord_2599912) baseStart_2599912 baseEnd_2599912 := by
    simpa [prefixWord, tailWord_2599912, baseEnd_2599912] using wordTrace_append hprefix tailTrace_2599912
  have hstable : (prefixWord ++ tailWord_2599912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599912).length < 2 ^ (prefixWord ++ tailWord_2599912).sum := by decide
  have hdescent : baseEnd_2599912 < baseStart_2599912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2599972 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_2599972 : Nat := 118140960795 + 2599972 * 2 ^ 59
def prefixEnd_2599972 : Nat := 4983230072969 + 3 ^ 40 * 2599972 * 2
def baseEnd_2599972 : Nat := 890023549487737887528635

theorem tailTrace_2599972 : CollatzResearch.WordTrace tailWord_2599972 prefixEnd_2599972 890023549487737887528635 := by
  unfold tailWord_2599972
  simp only [CollatzResearch.WordTrace]
  refine ⟨47414384668376479355445085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63219179557835305807260113 47414384668376479355445085)
  ·
    refine ⟨17780394250641179758291907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47414384668376479355445085 17780394250641179758291907)
    ·
      refine ⟨26670591375961769637437861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17780394250641179758291907 26670591375961769637437861)
      ·
        refine ⟨5000735882992831807019599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26670591375961769637437861 5000735882992831807019599)
        ·
          refine ⟨7501103824489247710529399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000735882992831807019599 7501103824489247710529399)
          ·
            refine ⟨11251655736733871565794099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501103824489247710529399 11251655736733871565794099)
            ·
              refine ⟨16877483605100807348691149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11251655736733871565794099 16877483605100807348691149)
              ·
                refine ⟨6329056351912802755759181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16877483605100807348691149 6329056351912802755759181)
                ·
                  refine ⟨2373396131967301033409693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6329056351912802755759181 2373396131967301033409693)
                  ·
                    refine ⟨890023549487737887528635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2373396131967301033409693 890023549487737887528635)
                    ·
                      rfl

theorem cell22_2599972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_2599972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2599972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2599972 prefixEnd_2599972 := by exact prefixLift 2599972
  have htrace : WordTrace (prefixWord ++ tailWord_2599972) baseStart_2599972 baseEnd_2599972 := by
    simpa [prefixWord, tailWord_2599972, baseEnd_2599972] using wordTrace_append hprefix tailTrace_2599972
  have hstable : (prefixWord ++ tailWord_2599972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2599972).length < 2 ^ (prefixWord ++ tailWord_2599972).sum := by decide
  have hdescent : baseEnd_2599972 < baseStart_2599972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2599972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600092 : List Nat := [2, 2, 3, 2, 1, 4, 1, 7]
def baseStart_2600092 : Nat := 118140960795 + 2600092 * 2 ^ 59
def prefixEnd_2600092 : Nat := 4983230072969 + 3 ^ 40 * 2600092 * 2
def baseEnd_2600092 : Nat := 98896069771121952725363

theorem tailTrace_2600092 : CollatzResearch.WordTrace tailWord_2600092 prefixEnd_2600092 98896069771121952725363 := by
  unfold tailWord_2600092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47416573048159109602629265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63222097397545479470172353 47416573048159109602629265)
  ·
    refine ⟨35562429786119332201971949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47416573048159109602629265 35562429786119332201971949)
    ·
      refine ⟨13335911169794749575739481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35562429786119332201971949 13335911169794749575739481)
      ·
        refine ⟨10001933377346062181804611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13335911169794749575739481 10001933377346062181804611)
        ·
          refine ⟨15002900066019093272706917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10001933377346062181804611 15002900066019093272706917)
          ·
            refine ⟨2813043762378579988632547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15002900066019093272706917 2813043762378579988632547)
            ·
              refine ⟨4219565643567869982948821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813043762378579988632547 4219565643567869982948821)
              ·
                refine ⟨98896069771121952725363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4219565643567869982948821 98896069771121952725363)
                ·
                  rfl

theorem cell22_2600092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 7].length) (baseStart_2600092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600092 prefixEnd_2600092 := by exact prefixLift 2600092
  have htrace : WordTrace (prefixWord ++ tailWord_2600092) baseStart_2600092 baseEnd_2600092 := by
    simpa [prefixWord, tailWord_2600092, baseEnd_2600092] using wordTrace_append hprefix tailTrace_2600092
  have hstable : (prefixWord ++ tailWord_2600092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600092).length < 2 ^ (prefixWord ++ tailWord_2600092).sum := by decide
  have hdescent : baseEnd_2600092 < baseStart_2600092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600109 : List Nat := [1, 5, 2, 1, 3, 1, 3, 6]
def baseStart_2600109 : Nat := 118140960795 + 2600109 * 2 ^ 59
def prefixEnd_2600109 : Nat := 4983230072969 + 3 ^ 40 * 2600109 * 2
def baseEnd_2600109 : Nat := 98896716376390577428135

theorem tailTrace_2600109 : CollatzResearch.WordTrace tailWord_2600109 prefixEnd_2600109 98896716376390577428135 := by
  unfold tailWord_2600109
  simp only [CollatzResearch.WordTrace]
  refine ⟨94833766137256631108627381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63222510758171087405751587 94833766137256631108627381)
  ·
    refine ⟨8890665575367809166433817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94833766137256631108627381 8890665575367809166433817)
    ·
      refine ⟨6667999181525856874825363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8890665575367809166433817 6667999181525856874825363)
      ·
        refine ⟨10001998772288785312238045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6667999181525856874825363 10001998772288785312238045)
        ·
          refine ⟨3750749539608294492089267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10001998772288785312238045 3750749539608294492089267)
          ·
            refine ⟨5626124309412441738133901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750749539608294492089267 5626124309412441738133901)
            ·
              refine ⟨2109796616029665651800213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5626124309412441738133901 2109796616029665651800213)
              ·
                refine ⟨98896716376390577428135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2109796616029665651800213 98896716376390577428135)
                ·
                  rfl

theorem cell22_2600109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 6].length) (baseStart_2600109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600109 prefixEnd_2600109 := by exact prefixLift 2600109
  have htrace : WordTrace (prefixWord ++ tailWord_2600109) baseStart_2600109 baseEnd_2600109 := by
    simpa [prefixWord, tailWord_2600109, baseEnd_2600109] using wordTrace_append hprefix tailTrace_2600109
  have hstable : (prefixWord ++ tailWord_2600109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600109).length < 2 ^ (prefixWord ++ tailWord_2600109).sum := by decide
  have hdescent : baseEnd_2600109 < baseStart_2600109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600130 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2600130 : Nat := 118140960795 + 2600130 * 2 ^ 59
def prefixEnd_2600130 : Nat := 4983230072969 + 3 ^ 40 * 2600130 * 2
def baseEnd_2600130 : Nat := 890077636116678142078151

theorem tailTrace_2600130 : CollatzResearch.WordTrace tailWord_2600130 prefixEnd_2600130 890077636116678142078151 := by
  unfold tailWord_2600130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23708633017545137923785461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63223021380120367796761229 23708633017545137923785461)
  ·
    refine ⟨2222684345394856680354887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23708633017545137923785461 2222684345394856680354887)
    ·
      refine ⟨3334026518092285020532331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2222684345394856680354887 3334026518092285020532331)
      ·
        refine ⟨5001039777138427530798497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3334026518092285020532331 5001039777138427530798497)
        ·
          refine ⟨3750779832853820648098873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5001039777138427530798497 3750779832853820648098873)
          ·
            refine ⟨2813084874640365486074155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3750779832853820648098873 2813084874640365486074155)
            ·
              refine ⟨4219627311960548229111233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813084874640365486074155 4219627311960548229111233)
              ·
                refine ⟨3164720483970411171833425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219627311960548229111233 3164720483970411171833425)
                ·
                  refine ⟨2373540362977808378875069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164720483970411171833425 2373540362977808378875069)
                  ·
                    refine ⟨890077636116678142078151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2373540362977808378875069 890077636116678142078151)
                    ·
                      rfl

theorem cell22_2600130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2600130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600130 prefixEnd_2600130 := by exact prefixLift 2600130
  have htrace : WordTrace (prefixWord ++ tailWord_2600130) baseStart_2600130 baseEnd_2600130 := by
    simpa [prefixWord, tailWord_2600130, baseEnd_2600130] using wordTrace_append hprefix tailTrace_2600130
  have hstable : (prefixWord ++ tailWord_2600130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600130).length < 2 ^ (prefixWord ++ tailWord_2600130).sum := by decide
  have hdescent : baseEnd_2600130 < baseStart_2600130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600197 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_2600197 : Nat := 118140960795 + 2600197 * 2 ^ 59
def prefixEnd_2600197 : Nat := 4983230072969 + 3 ^ 40 * 2600197 * 2
def baseEnd_2600197 : Nat := 890100571585912300652945

theorem tailTrace_2600197 : CollatzResearch.WordTrace tailWord_2600197 prefixEnd_2600197 890100571585912300652945 := by
  unfold tailWord_2600197
  simp only [CollatzResearch.WordTrace]
  refine ⟨94836975760937822137830845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63224650507291881425220563 94836975760937822137830845)
  ·
    refine ⟨35563865910351683301686567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94836975760937822137830845 35563865910351683301686567)
    ·
      refine ⟨53345798865527524952529851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35563865910351683301686567 53345798865527524952529851)
      ·
        refine ⟨80018698298291287428794777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53345798865527524952529851 80018698298291287428794777)
        ·
          refine ⟨60014023723718465571596083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80018698298291287428794777 60014023723718465571596083)
          ·
            refine ⟨90021035585577698357394125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60014023723718465571596083 90021035585577698357394125)
            ·
              refine ⟨33757888344591636884022797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90021035585577698357394125 33757888344591636884022797)
              ·
                refine ⟨12659208129221863831508549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33757888344591636884022797 12659208129221863831508549)
                ·
                  refine ⟨2373601524229099468407853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12659208129221863831508549 2373601524229099468407853)
                  ·
                    refine ⟨890100571585912300652945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2373601524229099468407853 890100571585912300652945)
                    ·
                      rfl

theorem cell22_2600197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_2600197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600197 prefixEnd_2600197 := by exact prefixLift 2600197
  have htrace : WordTrace (prefixWord ++ tailWord_2600197) baseStart_2600197 baseEnd_2600197 := by
    simpa [prefixWord, tailWord_2600197, baseEnd_2600197] using wordTrace_append hprefix tailTrace_2600197
  have hstable : (prefixWord ++ tailWord_2600197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600197).length < 2 ^ (prefixWord ++ tailWord_2600197).sum := by decide
  have hdescent : baseEnd_2600197 < baseStart_2600197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600229 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_2600229 : Nat := 118140960795 + 2600229 * 2 ^ 59
def prefixEnd_2600229 : Nat := 4983230072969 + 3 ^ 40 * 2600229 * 2
def baseEnd_2600229 : Nat := 890111525839874883852847

theorem tailTrace_2600229 : CollatzResearch.WordTrace tailWord_2600229 prefixEnd_2600229 890111525839874883852847 := by
  unfold tailWord_2600229
  simp only [CollatzResearch.WordTrace]
  refine ⟨94838142896821891602995741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63225428597881261068663827 94838142896821891602995741)
  ·
    refine ⟨35564303586308209351123403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94838142896821891602995741 35564303586308209351123403)
    ·
      refine ⟨53346455379462314026685105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35564303586308209351123403 53346455379462314026685105)
      ·
        refine ⟨40009841534596735520013829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53346455379462314026685105 40009841534596735520013829)
        ·
          refine ⟨7501845287736887910002593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40009841534596735520013829 7501845287736887910002593)
          ·
            refine ⟨5626383965802665932501945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7501845287736887910002593 5626383965802665932501945)
            ·
              refine ⟨4219787974351999449376459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5626383965802665932501945 4219787974351999449376459)
              ·
                refine ⟨6329681961527999174064689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219787974351999449376459 6329681961527999174064689)
                ·
                  refine ⟨4747261471145999380548517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6329681961527999174064689 4747261471145999380548517)
                  ·
                    refine ⟨890111525839874883852847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747261471145999380548517 890111525839874883852847)
                    ·
                      rfl

theorem cell22_2600229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_2600229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600229 prefixEnd_2600229 := by exact prefixLift 2600229
  have htrace : WordTrace (prefixWord ++ tailWord_2600229) baseStart_2600229 baseEnd_2600229 := by
    simpa [prefixWord, tailWord_2600229, baseEnd_2600229] using wordTrace_append hprefix tailTrace_2600229
  have hstable : (prefixWord ++ tailWord_2600229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600229).length < 2 ^ (prefixWord ++ tailWord_2600229).sum := by decide
  have hdescent : baseEnd_2600229 < baseStart_2600229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600272 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_2600272 : Nat := 118140960795 + 2600272 * 2 ^ 59
def prefixEnd_2600272 : Nat := 4983230072969 + 3 ^ 40 * 2600272 * 2
def baseEnd_2600272 : Nat := 296708748539545701675905

theorem tailTrace_2600272 : CollatzResearch.WordTrace tailWord_2600272 prefixEnd_2600272 296708748539545701675905 := by
  unfold tailWord_2600272
  simp only [CollatzResearch.WordTrace]
  refine ⟨47419855617833054973405535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63226474157110739964540713 47419855617833054973405535)
  ·
    refine ⟨71129783426749582460108303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47419855617833054973405535 71129783426749582460108303)
    ·
      refine ⟨106694675140124373690162455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71129783426749582460108303 106694675140124373690162455)
      ·
        refine ⟨160042012710186560535243683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106694675140124373690162455 160042012710186560535243683)
        ·
          refine ⟨240063019065279840802865525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160042012710186560535243683 240063019065279840802865525)
          ·
            refine ⟨22505908037369985075268643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 240063019065279840802865525 22505908037369985075268643)
            ·
              refine ⟨33758862056054977612902965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22505908037369985075268643 33758862056054977612902965)
              ·
                refine ⟨3164893317755154151209653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33758862056054977612902965 3164893317755154151209653)
                ·
                  refine ⟨296708748539545701675905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3164893317755154151209653 296708748539545701675905)
                  ·
                    rfl

theorem cell22_2600272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_2600272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600272 prefixEnd_2600272 := by exact prefixLift 2600272
  have htrace : WordTrace (prefixWord ++ tailWord_2600272) baseStart_2600272 baseEnd_2600272 := by
    simpa [prefixWord, tailWord_2600272, baseEnd_2600272] using wordTrace_append hprefix tailTrace_2600272
  have hstable : (prefixWord ++ tailWord_2600272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600272).length < 2 ^ (prefixWord ++ tailWord_2600272).sum := by decide
  have hdescent : baseEnd_2600272 < baseStart_2600272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600351 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 4]
def baseStart_2600351 : Nat := 118140960795 + 2600351 * 2 ^ 59
def prefixEnd_2600351 : Nat := 4983230072969 + 3 ^ 40 * 2600351 * 2
def baseEnd_2600351 : Nat := 296717762977702410767491

theorem tailTrace_2600351 : CollatzResearch.WordTrace tailWord_2600351 prefixEnd_2600351 296717762977702410767491 := by
  unfold tailWord_2600351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94842592602379906438936907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63228395068253270959291271 94842592602379906438936907)
  ·
    refine ⟨142263888903569859658405361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94842592602379906438936907 142263888903569859658405361)
    ·
      refine ⟨106697916677677394743804021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142263888903569859658405361 106697916677677394743804021)
      ·
        refine ⟨10002929688532255757231627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106697916677677394743804021 10002929688532255757231627)
        ·
          refine ⟨15004394532798383635847441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10002929688532255757231627 15004394532798383635847441)
          ·
            refine ⟨11253295899598787726885581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15004394532798383635847441 11253295899598787726885581)
            ·
              refine ⟨4219985962349545397582093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11253295899598787726885581 4219985962349545397582093)
              ·
                refine ⟨1582494735881079524093285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4219985962349545397582093 1582494735881079524093285)
                ·
                  refine ⟨296717762977702410767491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1582494735881079524093285 296717762977702410767491)
                  ·
                    rfl

theorem cell22_2600351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 4].length) (baseStart_2600351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600351 prefixEnd_2600351 := by exact prefixLift 2600351
  have htrace : WordTrace (prefixWord ++ tailWord_2600351) baseStart_2600351 baseEnd_2600351 := by
    simpa [prefixWord, tailWord_2600351, baseEnd_2600351] using wordTrace_append hprefix tailTrace_2600351
  have hstable : (prefixWord ++ tailWord_2600351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600351).length < 2 ^ (prefixWord ++ tailWord_2600351).sum := by decide
  have hdescent : baseEnd_2600351 < baseStart_2600351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600407 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 9]
def baseStart_2600407 : Nat := 118140960795 + 2600407 * 2 ^ 59
def prefixEnd_2600407 : Nat := 4983230072969 + 3 ^ 40 * 2600407 * 2
def baseEnd_2600407 : Nat := 296724152959180584300767

theorem tailTrace_2600407 : CollatzResearch.WordTrace tailWord_2600407 prefixEnd_2600407 296724152959180584300767 := by
  unfold tailWord_2600407
  simp only [CollatzResearch.WordTrace]
  refine ⟨94844635090177028002975475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63229756726784685335316983 94844635090177028002975475)
  ·
    refine ⟨142266952635265542004463213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94844635090177028002975475 142266952635265542004463213)
    ·
      refine ⟨53350107238224578251673705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142266952635265542004463213 53350107238224578251673705)
      ·
        refine ⟨40012580428668433688755279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53350107238224578251673705 40012580428668433688755279)
        ·
          refine ⟨60018870643002650533132919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40012580428668433688755279 60018870643002650533132919)
          ·
            refine ⟨90028305964503975799699379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60018870643002650533132919 90028305964503975799699379)
            ·
              refine ⟨135042458946755963699549069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90028305964503975799699379 135042458946755963699549069)
              ·
                refine ⟨50640922105033486387330901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135042458946755963699549069 50640922105033486387330901)
                ·
                  refine ⟨296724152959180584300767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50640922105033486387330901 296724152959180584300767)
                  ·
                    rfl

theorem cell22_2600407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_2600407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600407 prefixEnd_2600407 := by exact prefixLift 2600407
  have htrace : WordTrace (prefixWord ++ tailWord_2600407) baseStart_2600407 baseEnd_2600407 := by
    simpa [prefixWord, tailWord_2600407, baseEnd_2600407] using wordTrace_append hprefix tailTrace_2600407
  have hstable : (prefixWord ++ tailWord_2600407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600407).length < 2 ^ (prefixWord ++ tailWord_2600407).sum := by decide
  have hdescent : baseEnd_2600407 < baseStart_2600407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600499 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_2600499 : Nat := 118140960795 + 2600499 * 2 ^ 59
def prefixEnd_2600499 : Nat := 4983230072969 + 3 ^ 40 * 2600499 * 2
def baseEnd_2600499 : Nat := 890203952357684179602019

theorem tailTrace_2600499 : CollatzResearch.WordTrace tailWord_2600499 prefixEnd_2600499 890203952357684179602019 := by
  unfold tailWord_2600499
  simp only [CollatzResearch.WordTrace]
  refine ⟨94847990605843727715324551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63231993737229151810216367 94847990605843727715324551)
  ·
    refine ⟨142271985908765591572986827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94847990605843727715324551 142271985908765591572986827)
    ·
      refine ⟨213407978863148387359480241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142271985908765591572986827 213407978863148387359480241)
      ·
        refine ⟨160055984147361290519610181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213407978863148387359480241 160055984147361290519610181)
        ·
          refine ⟨30010497027630241972426909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160055984147361290519610181 30010497027630241972426909)
          ·
            refine ⟨11253936385361340739660091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30010497027630241972426909 11253936385361340739660091)
            ·
              refine ⟨16880904578042011109490137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11253936385361340739660091 16880904578042011109490137)
              ·
                refine ⟨12660678433531508332117603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16880904578042011109490137 12660678433531508332117603)
                ·
                  refine ⟨18991017650297262498176405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12660678433531508332117603 18991017650297262498176405)
                  ·
                    refine ⟨890203952357684179602019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18991017650297262498176405 890203952357684179602019)
                    ·
                      rfl

theorem cell22_2600499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_2600499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600499 prefixEnd_2600499 := by exact prefixLift 2600499
  have htrace : WordTrace (prefixWord ++ tailWord_2600499) baseStart_2600499 baseEnd_2600499 := by
    simpa [prefixWord, tailWord_2600499, baseEnd_2600499] using wordTrace_append hprefix tailTrace_2600499
  have hstable : (prefixWord ++ tailWord_2600499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600499).length < 2 ^ (prefixWord ++ tailWord_2600499).sum := by decide
  have hdescent : baseEnd_2600499 < baseStart_2600499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600501 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2600501 : Nat := 118140960795 + 2600501 * 2 ^ 59
def prefixEnd_2600501 : Nat := 4983230072969 + 3 ^ 40 * 2600501 * 2
def baseEnd_2600501 : Nat := 890204636998556841052013

theorem tailTrace_2600501 : CollatzResearch.WordTrace tailWord_2600501 prefixEnd_2600501 890204636998556841052013 := by
  unfold tailWord_2600501
  simp only [CollatzResearch.WordTrace]
  refine ⟨94848063551836482056897357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63232042367890988037931571 94848063551836482056897357)
  ·
    refine ⟨35568023831938680771336509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94848063551836482056897357 35568023831938680771336509)
    ·
      refine ⟨13338008936977005289251191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35568023831938680771336509 13338008936977005289251191)
      ·
        refine ⟨20007013405465507933876787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13338008936977005289251191 20007013405465507933876787)
        ·
          refine ⟨30010520108198261900815181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20007013405465507933876787 30010520108198261900815181)
          ·
            refine ⟨11253945040574348212805693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30010520108198261900815181 11253945040574348212805693)
            ·
              refine ⟨4220229390215380579802135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11253945040574348212805693 4220229390215380579802135)
              ·
                refine ⟨6330344085323070869703203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220229390215380579802135 6330344085323070869703203)
                ·
                  refine ⟨9495516127984606304554805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330344085323070869703203 9495516127984606304554805)
                  ·
                    refine ⟨890204636998556841052013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9495516127984606304554805 890204636998556841052013)
                    ·
                      rfl

theorem cell22_2600501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2600501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600501 prefixEnd_2600501 := by exact prefixLift 2600501
  have htrace : WordTrace (prefixWord ++ tailWord_2600501) baseStart_2600501 baseEnd_2600501 := by
    simpa [prefixWord, tailWord_2600501, baseEnd_2600501] using wordTrace_append hprefix tailTrace_2600501
  have hstable : (prefixWord ++ tailWord_2600501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600501).length < 2 ^ (prefixWord ++ tailWord_2600501).sum := by decide
  have hdescent : baseEnd_2600501 < baseStart_2600501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600544 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_2600544 : Nat := 118140960795 + 2600544 * 2 ^ 59
def prefixEnd_2600544 : Nat := 4983230072969 + 3 ^ 40 * 2600544 * 2
def baseEnd_2600544 : Nat := 890219356777319062226881

theorem tailTrace_2600544 : CollatzResearch.WordTrace tailWord_2600544 prefixEnd_2600544 890219356777319062226881 := by
  unfold tailWord_2600544
  simp only [CollatzResearch.WordTrace]
  refine ⟨47424815945340350200356343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63233087927120466933808457 47424815945340350200356343)
  ·
    refine ⟨71137223918010525300534515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47424815945340350200356343 71137223918010525300534515)
    ·
      refine ⟨106705835877015787950801773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71137223918010525300534515 106705835877015787950801773)
      ·
        refine ⟨40014688453880920481550665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106705835877015787950801773 40014688453880920481550665)
        ·
          refine ⟨30011016340410690361162999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40014688453880920481550665 30011016340410690361162999)
          ·
            refine ⟨45016524510616035541744499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30011016340410690361162999 45016524510616035541744499)
            ·
              refine ⟨67524786765924053312616749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45016524510616035541744499 67524786765924053312616749)
              ·
                refine ⟨25321795037221519992231281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67524786765924053312616749 25321795037221519992231281)
                ·
                  refine ⟨18991346277916139994173461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25321795037221519992231281 18991346277916139994173461)
                  ·
                    refine ⟨890219356777319062226881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18991346277916139994173461 890219356777319062226881)
                    ·
                      rfl

theorem cell22_2600544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_2600544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600544 prefixEnd_2600544 := by exact prefixLift 2600544
  have htrace : WordTrace (prefixWord ++ tailWord_2600544) baseStart_2600544 baseEnd_2600544 := by
    simpa [prefixWord, tailWord_2600544, baseEnd_2600544] using wordTrace_append hprefix tailTrace_2600544
  have hstable : (prefixWord ++ tailWord_2600544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600544).length < 2 ^ (prefixWord ++ tailWord_2600544).sum := by decide
  have hdescent : baseEnd_2600544 < baseStart_2600544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600552 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2600552 : Nat := 118140960795 + 2600552 * 2 ^ 59
def prefixEnd_2600552 : Nat := 4983230072969 + 3 ^ 40 * 2600552 * 2
def baseEnd_2600552 : Nat := 890222095340809708026857

theorem tailTrace_2600552 : CollatzResearch.WordTrace tailWord_2600552 prefixEnd_2600552 890222095340809708026857 := by
  unfold tailWord_2600552
  simp only [CollatzResearch.WordTrace]
  refine ⟨47424961837325858883501955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63233282449767811844669273 47424961837325858883501955)
  ·
    refine ⟨71137442755988788325252933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47424961837325858883501955 71137442755988788325252933)
    ·
      refine ⟨13338270516747897810984925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71137442755988788325252933 13338270516747897810984925)
      ·
        refine ⟨5001851443780461679119347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13338270516747897810984925 5001851443780461679119347)
        ·
          refine ⟨7502777165670692518679021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5001851443780461679119347 7502777165670692518679021)
          ·
            refine ⟨2813541437126509694504633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7502777165670692518679021 2813541437126509694504633)
            ·
              refine ⟨2110156077844882270878475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2813541437126509694504633 2110156077844882270878475)
              ·
                refine ⟨3165234116767323406317713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110156077844882270878475 3165234116767323406317713)
                ·
                  refine ⟨2373925587575492554738285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165234116767323406317713 2373925587575492554738285)
                  ·
                    refine ⟨890222095340809708026857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2373925587575492554738285 890222095340809708026857)
                    ·
                      rfl

theorem cell22_2600552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2600552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600552 prefixEnd_2600552 := by exact prefixLift 2600552
  have htrace : WordTrace (prefixWord ++ tailWord_2600552) baseStart_2600552 baseEnd_2600552 := by
    simpa [prefixWord, tailWord_2600552, baseEnd_2600552] using wordTrace_append hprefix tailTrace_2600552
  have hstable : (prefixWord ++ tailWord_2600552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600552).length < 2 ^ (prefixWord ++ tailWord_2600552).sum := by decide
  have hdescent : baseEnd_2600552 < baseStart_2600552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600651 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 2, 4]
def baseStart_2600651 : Nat := 118140960795 + 2600651 * 2 ^ 59
def prefixEnd_2600651 : Nat := 4983230072969 + 3 ^ 40 * 2600651 * 2
def baseEnd_2600651 : Nat := 890255985064006449801553

theorem tailTrace_2600651 : CollatzResearch.WordTrace tailWord_2600651 prefixEnd_2600651 890255985064006449801553 := by
  unfold tailWord_2600651
  simp only [CollatzResearch.WordTrace]
  refine ⟨94853534501293057674857807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63235689667528705116571871 94853534501293057674857807)
  ·
    refine ⟨142280301751939586512286711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94853534501293057674857807 142280301751939586512286711)
    ·
      refine ⟨213420452627909379768430067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142280301751939586512286711 213420452627909379768430067)
      ·
        refine ⟨320130678941864069652645101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213420452627909379768430067 320130678941864069652645101)
        ·
          refine ⟨120049004603199026119741913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320130678941864069652645101 120049004603199026119741913)
          ·
            refine ⟨90036753452399269589806435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120049004603199026119741913 90036753452399269589806435)
            ·
              refine ⟨135055130178598904384709653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90036753452399269589806435 135055130178598904384709653)
              ·
                refine ⟨6330709227121823643033265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135055130178598904384709653 6330709227121823643033265)
                ·
                  refine ⟨4748031920341367732274949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6330709227121823643033265 4748031920341367732274949)
                  ·
                    refine ⟨890255985064006449801553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4748031920341367732274949 890255985064006449801553)
                    ·
                      rfl

theorem cell22_2600651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_2600651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600651 prefixEnd_2600651 := by exact prefixLift 2600651
  have htrace : WordTrace (prefixWord ++ tailWord_2600651) baseStart_2600651 baseEnd_2600651 := by
    simpa [prefixWord, tailWord_2600651, baseEnd_2600651] using wordTrace_append hprefix tailTrace_2600651
  have hstable : (prefixWord ++ tailWord_2600651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600651).length < 2 ^ (prefixWord ++ tailWord_2600651).sum := by decide
  have hdescent : baseEnd_2600651 < baseStart_2600651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600715 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 1, 3]
def baseStart_2600715 : Nat := 118140960795 + 2600715 * 2 ^ 59
def prefixEnd_2600715 : Nat := 4983230072969 + 3 ^ 40 * 2600715 * 2
def baseEnd_2600715 : Nat := 890277893571931616201357

theorem tailTrace_2600715 : CollatzResearch.WordTrace tailWord_2600715 prefixEnd_2600715 890277893571931616201357 := by
  unfold tailWord_2600715
  simp only [CollatzResearch.WordTrace]
  refine ⟨94855868773061196605187599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63237245848707464403458399 94855868773061196605187599)
  ·
    refine ⟨142283803159591794907781399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94855868773061196605187599 142283803159591794907781399)
    ·
      refine ⟨213425704739387692361672099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142283803159591794907781399 213425704739387692361672099)
      ·
        refine ⟨320138557109081538542508149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213425704739387692361672099 320138557109081538542508149)
        ·
          refine ⟨30012989728976394238360139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 320138557109081538542508149 30012989728976394238360139)
          ·
            refine ⟨45019484593464591357540209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30012989728976394238360139 45019484593464591357540209)
            ·
              refine ⟨33764613445098443518155157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45019484593464591357540209 33764613445098443518155157)
              ·
                refine ⟨1582716255238989539913523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33764613445098443518155157 1582716255238989539913523)
                ·
                  refine ⟨2374074382858484309870285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582716255238989539913523 2374074382858484309870285)
                  ·
                    refine ⟨890277893571931616201357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374074382858484309870285 890277893571931616201357)
                    ·
                      rfl

theorem cell22_2600715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 3].length) (baseStart_2600715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600715 prefixEnd_2600715 := by exact prefixLift 2600715
  have htrace : WordTrace (prefixWord ++ tailWord_2600715) baseStart_2600715 baseEnd_2600715 := by
    simpa [prefixWord, tailWord_2600715, baseEnd_2600715] using wordTrace_append hprefix tailTrace_2600715
  have hstable : (prefixWord ++ tailWord_2600715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600715).length < 2 ^ (prefixWord ++ tailWord_2600715).sum := by decide
  have hdescent : baseEnd_2600715 < baseStart_2600715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600766 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_2600766 : Nat := 118140960795 + 2600766 * 2 ^ 59
def prefixEnd_2600766 : Nat := 4983230072969 + 3 ^ 40 * 2600766 * 2
def baseEnd_2600766 : Nat := 890295351914184483176201

theorem tailTrace_2600766 : CollatzResearch.WordTrace tailWord_2600766 prefixEnd_2600766 890295351914184483176201 := by
  unfold tailWord_2600766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11857216111984554039411769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63238485930584288210196101 11857216111984554039411769)
  ·
    refine ⟨8892912083988415529558827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11857216111984554039411769 8892912083988415529558827)
    ·
      refine ⟨13339368125982623294338241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8892912083988415529558827 13339368125982623294338241)
      ·
        refine ⟨10004526094486967470753681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13339368125982623294338241 10004526094486967470753681)
        ·
          refine ⟨7503394570865225603065261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10004526094486967470753681 7503394570865225603065261)
          ·
            refine ⟨2813772964074459601149473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7503394570865225603065261 2813772964074459601149473)
            ·
              refine ⟨2110329723055844700862105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2813772964074459601149473 2110329723055844700862105)
              ·
                refine ⟨1582747292291883525646579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110329723055844700862105 1582747292291883525646579)
                ·
                  refine ⟨2374120938437825288469869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582747292291883525646579 2374120938437825288469869)
                  ·
                    refine ⟨890295351914184483176201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374120938437825288469869 890295351914184483176201)
                    ·
                      rfl

theorem cell22_2600766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_2600766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600766 prefixEnd_2600766 := by exact prefixLift 2600766
  have htrace : WordTrace (prefixWord ++ tailWord_2600766) baseStart_2600766 baseEnd_2600766 := by
    simpa [prefixWord, tailWord_2600766, baseEnd_2600766] using wordTrace_append hprefix tailTrace_2600766
  have hstable : (prefixWord ++ tailWord_2600766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600766).length < 2 ^ (prefixWord ++ tailWord_2600766).sum := by decide
  have hdescent : baseEnd_2600766 < baseStart_2600766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600839 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2600839 : Nat := 118140960795 + 2600839 * 2 ^ 59
def prefixEnd_2600839 : Nat := 4983230072969 + 3 ^ 40 * 2600839 * 2
def baseEnd_2600839 : Nat := 890320341306036626100977

theorem tailTrace_2600839 : CollatzResearch.WordTrace tailWord_2600839 prefixEnd_2600839 890320341306036626100977 := by
  unfold tailWord_2600839
  simp only [CollatzResearch.WordTrace]
  refine ⟨94860391424611965782701571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63240260949741310521801047 94860391424611965782701571)
  ·
    refine ⟨142290587136917948674052357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94860391424611965782701571 142290587136917948674052357)
    ·
      refine ⟨26679485088172115376384817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142290587136917948674052357 26679485088172115376384817)
      ·
        refine ⟨20009613816129086532288613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26679485088172115376384817 20009613816129086532288613)
        ·
          refine ⟨3751802590524203724804115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20009613816129086532288613 3751802590524203724804115)
          ·
            refine ⟨5627703885786305587206173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751802590524203724804115 5627703885786305587206173)
            ·
              refine ⟨2110388957169864595202315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5627703885786305587206173 2110388957169864595202315)
              ·
                refine ⟨3165583435754796892803473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110388957169864595202315 3165583435754796892803473)
                ·
                  refine ⟨2374187576816097669602605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165583435754796892803473 2374187576816097669602605)
                  ·
                    refine ⟨890320341306036626100977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374187576816097669602605 890320341306036626100977)
                    ·
                      rfl

theorem cell22_2600839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2600839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600839 prefixEnd_2600839 := by exact prefixLift 2600839
  have htrace : WordTrace (prefixWord ++ tailWord_2600839) baseStart_2600839 baseEnd_2600839 := by
    simpa [prefixWord, tailWord_2600839, baseEnd_2600839] using wordTrace_append hprefix tailTrace_2600839
  have hstable : (prefixWord ++ tailWord_2600839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600839).length < 2 ^ (prefixWord ++ tailWord_2600839).sum := by decide
  have hdescent : baseEnd_2600839 < baseStart_2600839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600852 : List Nat := [2, 4, 2, 1, 1, 4, 2, 6]
def baseStart_2600852 : Nat := 118140960795 + 2600852 * 2 ^ 59
def prefixEnd_2600852 : Nat := 4983230072969 + 3 ^ 40 * 2600852 * 2
def baseEnd_2600852 : Nat := 98924976830189880613993

theorem tailTrace_2600852 : CollatzResearch.WordTrace tailWord_2600852 prefixEnd_2600852 98924976830189880613993 := by
  unfold tailWord_2600852
  simp only [CollatzResearch.WordTrace]
  refine ⟨47430432786782434501462405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63240577049043246001949873 47430432786782434501462405)
  ·
    refine ⟨8893206147521706469024201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47430432786782434501462405 8893206147521706469024201)
    ·
      refine ⟨6669904610641279851768151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8893206147521706469024201 6669904610641279851768151)
      ·
        refine ⟨10004856915961919777652227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6669904610641279851768151 10004856915961919777652227)
        ·
          refine ⟨15007285373942879666478341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004856915961919777652227 15007285373942879666478341)
          ·
            refine ⟨2813866007614289937464689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15007285373942879666478341 2813866007614289937464689)
            ·
              refine ⟨2110399505710717453098517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2813866007614289937464689 2110399505710717453098517)
              ·
                refine ⟨98924976830189880613993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2110399505710717453098517 98924976830189880613993)
                ·
                  rfl

theorem cell22_2600852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 6].length) (baseStart_2600852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600852 prefixEnd_2600852 := by exact prefixLift 2600852
  have htrace : WordTrace (prefixWord ++ tailWord_2600852) baseStart_2600852 baseEnd_2600852 := by
    simpa [prefixWord, tailWord_2600852, baseEnd_2600852] using wordTrace_append hprefix tailTrace_2600852
  have hstable : (prefixWord ++ tailWord_2600852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600852).length < 2 ^ (prefixWord ++ tailWord_2600852).sum := by decide
  have hdescent : baseEnd_2600852 < baseStart_2600852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600910 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_2600910 : Nat := 118140960795 + 2600910 * 2 ^ 59
def prefixEnd_2600910 : Nat := 4983230072969 + 3 ^ 40 * 2600910 * 2
def baseEnd_2600910 : Nat := 890344646057016107575759

theorem tailTrace_2600910 : CollatzResearch.WordTrace tailWord_2600910 prefixEnd_2600910 890344646057016107575759 := by
  unfold tailWord_2600910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11857872625919343113567023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63241987338236496605690789 11857872625919343113567023)
  ·
    refine ⟨17786808938879014670350535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11857872625919343113567023 17786808938879014670350535)
    ·
      refine ⟨26680213408318522005525803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17786808938879014670350535 26680213408318522005525803)
      ·
        refine ⟨40020320112477783008288705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26680213408318522005525803 40020320112477783008288705)
        ·
          refine ⟨30015240084358337256216529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40020320112477783008288705 30015240084358337256216529)
          ·
            refine ⟨22511430063268752942162397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30015240084358337256216529 22511430063268752942162397)
            ·
              refine ⟨8441786273725782353310899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22511430063268752942162397 8441786273725782353310899)
              ·
                refine ⟨12662679410588673529966349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8441786273725782353310899 12662679410588673529966349)
                ·
                  refine ⟨4748504778970752573737381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12662679410588673529966349 4748504778970752573737381)
                  ·
                    refine ⟨890344646057016107575759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4748504778970752573737381 890344646057016107575759)
                    ·
                      rfl

theorem cell22_2600910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_2600910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600910 prefixEnd_2600910 := by exact prefixLift 2600910
  have htrace : WordTrace (prefixWord ++ tailWord_2600910) baseStart_2600910 baseEnd_2600910 := by
    simpa [prefixWord, tailWord_2600910, baseEnd_2600910] using wordTrace_append hprefix tailTrace_2600910
  have hstable : (prefixWord ++ tailWord_2600910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600910).length < 2 ^ (prefixWord ++ tailWord_2600910).sum := by decide
  have hdescent : baseEnd_2600910 < baseStart_2600910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600940 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_2600940 : Nat := 118140960795 + 2600940 * 2 ^ 59
def prefixEnd_2600940 : Nat := 4983230072969 + 3 ^ 40 * 2600940 * 2
def baseEnd_2600940 : Nat := 890354915670106029325667

theorem tailTrace_2600940 : CollatzResearch.WordTrace tailWord_2600940 prefixEnd_2600940 890354915670106029325667 := by
  unfold tailWord_2600940
  simp only [CollatzResearch.WordTrace]
  refine ⟨47432037598623030016064137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63242716798164040021418849 47432037598623030016064137)
  ·
    refine ⟨35574028198967272512048103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47432037598623030016064137 35574028198967272512048103)
    ·
      refine ⟨53361042298450908768072155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35574028198967272512048103 53361042298450908768072155)
      ·
        refine ⟨80041563447676363152108233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53361042298450908768072155 80041563447676363152108233)
        ·
          refine ⟨60031172585757272364081175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80041563447676363152108233 60031172585757272364081175)
          ·
            refine ⟨90046758878635908546121763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60031172585757272364081175 90046758878635908546121763)
            ·
              refine ⟨135070138317953862819182645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90046758878635908546121763 135070138317953862819182645)
              ·
                refine ⟨12662825467308174639298373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135070138317953862819182645 12662825467308174639298373)
                ·
                  refine ⟨2374279775120282744868445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12662825467308174639298373 2374279775120282744868445)
                  ·
                    refine ⟨890354915670106029325667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374279775120282744868445 890354915670106029325667)
                    ·
                      rfl

theorem cell22_2600940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_2600940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600940 prefixEnd_2600940 := by exact prefixLift 2600940
  have htrace : WordTrace (prefixWord ++ tailWord_2600940) baseStart_2600940 baseEnd_2600940 := by
    simpa [prefixWord, tailWord_2600940, baseEnd_2600940] using wordTrace_append hprefix tailTrace_2600940
  have hstable : (prefixWord ++ tailWord_2600940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600940).length < 2 ^ (prefixWord ++ tailWord_2600940).sum := by decide
  have hdescent : baseEnd_2600940 < baseStart_2600940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600957 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_2600957 : Nat := 118140960795 + 2600957 * 2 ^ 59
def prefixEnd_2600957 : Nat := 4983230072969 + 3 ^ 40 * 2600957 * 2
def baseEnd_2600957 : Nat := 890360735117523651650615

theorem tailTrace_2600957 : CollatzResearch.WordTrace tailWord_2600957 prefixEnd_2600957 890360735117523651650615 := by
  unfold tailWord_2600957
  simp only [CollatzResearch.WordTrace]
  refine ⟨94864695238184471935497125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63243130158789647956998083 94864695238184471935497125)
  ·
    refine ⟨17787130357159588487905711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94864695238184471935497125 17787130357159588487905711)
    ·
      refine ⟨26680695535739382731858567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17787130357159588487905711 26680695535739382731858567)
      ·
        refine ⟨40021043303609074097787851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26680695535739382731858567 40021043303609074097787851)
        ·
          refine ⟨60031564955413611146681777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40021043303609074097787851 60031564955413611146681777)
          ·
            refine ⟨45023673716560208360011333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60031564955413611146681777 45023673716560208360011333)
            ·
              refine ⟨8441938821855039067502125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45023673716560208360011333 8441938821855039067502125)
              ·
                refine ⟨3165727058195639650313297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8441938821855039067502125 3165727058195639650313297)
                ·
                  refine ⟨2374295293646729737734973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165727058195639650313297 2374295293646729737734973)
                  ·
                    refine ⟨890360735117523651650615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374295293646729737734973 890360735117523651650615)
                    ·
                      rfl

theorem cell22_2600957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_2600957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600957 prefixEnd_2600957 := by exact prefixLift 2600957
  have htrace : WordTrace (prefixWord ++ tailWord_2600957) baseStart_2600957 baseEnd_2600957 := by
    simpa [prefixWord, tailWord_2600957, baseEnd_2600957] using wordTrace_append hprefix tailTrace_2600957
  have hstable : (prefixWord ++ tailWord_2600957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600957).length < 2 ^ (prefixWord ++ tailWord_2600957).sum := by decide
  have hdescent : baseEnd_2600957 < baseStart_2600957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2600985 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_2600985 : Nat := 118140960795 + 2600985 * 2 ^ 59
def prefixEnd_2600985 : Nat := 4983230072969 + 3 ^ 40 * 2600985 * 2
def baseEnd_2600985 : Nat := 890370320089740911950529

theorem tailTrace_2600985 : CollatzResearch.WordTrace tailWord_2600985 prefixEnd_2600985 890370320089740911950529 := by
  unfold tailWord_2600985
  simp only [CollatzResearch.WordTrace]
  refine ⟨94865716482083032717516409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63243810988055355145010939 94865716482083032717516409)
  ·
    refine ⟨71149287361562274538137307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94865716482083032717516409 71149287361562274538137307)
    ·
      refine ⟨106723931042343411807205961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71149287361562274538137307 106723931042343411807205961)
      ·
        refine ⟨80042948281757558855404471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106723931042343411807205961 80042948281757558855404471)
        ·
          refine ⟨120064422422636338283106707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80042948281757558855404471 120064422422636338283106707)
          ·
            refine ⟨180096633633954507424660061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120064422422636338283106707 180096633633954507424660061)
            ·
              refine ⟨67536237612732940284247523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180096633633954507424660061 67536237612732940284247523)
              ·
                refine ⟨101304356419099410426371285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67536237612732940284247523 101304356419099410426371285)
                ·
                  refine ⟨2374320853572642431868077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101304356419099410426371285 2374320853572642431868077)
                  ·
                    refine ⟨890370320089740911950529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374320853572642431868077 890370320089740911950529)
                    ·
                      rfl

theorem cell22_2600985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_2600985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2600985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2600985 prefixEnd_2600985 := by exact prefixLift 2600985
  have htrace : WordTrace (prefixWord ++ tailWord_2600985) baseStart_2600985 baseEnd_2600985 := by
    simpa [prefixWord, tailWord_2600985, baseEnd_2600985] using wordTrace_append hprefix tailTrace_2600985
  have hstable : (prefixWord ++ tailWord_2600985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2600985).length < 2 ^ (prefixWord ++ tailWord_2600985).sum := by decide
  have hdescent : baseEnd_2600985 < baseStart_2600985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2600985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601015 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 5]
def baseStart_2601015 : Nat := 118140960795 + 2601015 * 2 ^ 59
def prefixEnd_2601015 : Nat := 4983230072969 + 3 ^ 40 * 2601015 * 2
def baseEnd_2601015 : Nat := 296793529900943611233479

theorem tailTrace_2601015 : CollatzResearch.WordTrace tailWord_2601015 prefixEnd_2601015 296793529900943611233479 := by
  unfold tailWord_2601015
  simp only [CollatzResearch.WordTrace]
  refine ⟨94866810671974347841108499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63244540447982898560738999 94866810671974347841108499)
  ·
    refine ⟨142300216007961521761662749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94866810671974347841108499 142300216007961521761662749)
    ·
      refine ⟨53362581002985570660623531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142300216007961521761662749 53362581002985570660623531)
      ·
        refine ⟨80043871504478355990935297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53362581002985570660623531 80043871504478355990935297)
        ·
          refine ⟨60032903628358766993201473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80043871504478355990935297 60032903628358766993201473)
          ·
            refine ⟨45024677721269075244901105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60032903628358766993201473 45024677721269075244901105)
            ·
              refine ⟨33768508290951806433675829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45024677721269075244901105 33768508290951806433675829)
              ·
                refine ⟨3165797652276731853157109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33768508290951806433675829 3165797652276731853157109)
                ·
                  refine ⟨296793529900943611233479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3165797652276731853157109 296793529900943611233479)
                  ·
                    rfl

theorem cell22_2601015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 5].length) (baseStart_2601015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601015 prefixEnd_2601015 := by exact prefixLift 2601015
  have htrace : WordTrace (prefixWord ++ tailWord_2601015) baseStart_2601015 baseEnd_2601015 := by
    simpa [prefixWord, tailWord_2601015, baseEnd_2601015] using wordTrace_append hprefix tailTrace_2601015
  have hstable : (prefixWord ++ tailWord_2601015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601015).length < 2 ^ (prefixWord ++ tailWord_2601015).sum := by decide
  have hdescent : baseEnd_2601015 < baseStart_2601015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601066 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_2601066 : Nat := 118140960795 + 2601066 * 2 ^ 59
def prefixEnd_2601066 : Nat := 4983230072969 + 3 ^ 40 * 2601066 * 2
def baseEnd_2601066 : Nat := 296799349348361233558427

theorem tailTrace_2601066 : CollatzResearch.WordTrace tailWord_2601066 prefixEnd_2601066 296799349348361233558427 := by
  unfold tailWord_2601066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23717167698697395887803763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63245780529859722367476701 23717167698697395887803763)
  ·
    refine ⟨35575751548046093831705645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23717167698697395887803763 35575751548046093831705645)
    ·
      refine ⟨13340906830517285186889617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35575751548046093831705645 13340906830517285186889617)
      ·
        refine ⟨10005680122887963890167213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13340906830517285186889617 10005680122887963890167213)
        ·
          refine ⟨3752130046082986458812705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10005680122887963890167213 3752130046082986458812705)
          ·
            refine ⟨2814097534562239844109529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752130046082986458812705 2814097534562239844109529)
            ·
              refine ⟨2110573150921679883082147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814097534562239844109529 2110573150921679883082147)
              ·
                refine ⟨3165859726382519824623221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110573150921679883082147 3165859726382519824623221)
                ·
                  refine ⟨296799349348361233558427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3165859726382519824623221 296799349348361233558427)
                  ·
                    rfl

theorem cell22_2601066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_2601066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601066 prefixEnd_2601066 := by exact prefixLift 2601066
  have htrace : WordTrace (prefixWord ++ tailWord_2601066) baseStart_2601066 baseEnd_2601066 := by
    simpa [prefixWord, tailWord_2601066, baseEnd_2601066] using wordTrace_append hprefix tailTrace_2601066
  have hstable : (prefixWord ++ tailWord_2601066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601066).length < 2 ^ (prefixWord ++ tailWord_2601066).sum := by decide
  have hdescent : baseEnd_2601066 < baseStart_2601066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601079 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 1, 4]
def baseStart_2601079 : Nat := 118140960795 + 2601079 * 2 ^ 59
def prefixEnd_2601079 : Nat := 4983230072969 + 3 ^ 40 * 2601079 * 2
def baseEnd_2601079 : Nat := 890402498210756000100241

theorem tailTrace_2601079 : CollatzResearch.WordTrace tailWord_2601079 prefixEnd_2601079 890402498210756000100241 := by
  unfold tailWord_2601079
  simp only [CollatzResearch.WordTrace]
  refine ⟨94869144943742486771438291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63246096629161657847625527 94869144943742486771438291)
  ·
    refine ⟨142303717415613730157157437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94869144943742486771438291 142303717415613730157157437)
    ·
      refine ⟨53363894030855148808934039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142303717415613730157157437 53363894030855148808934039)
      ·
        refine ⟨80045841046282723213401059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53363894030855148808934039 80045841046282723213401059)
        ·
          refine ⟨120068761569424084820101589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80045841046282723213401059 120068761569424084820101589)
          ·
            refine ⟨2814111599283376987971131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 120068761569424084820101589 2814111599283376987971131)
            ·
              refine ⟨4221167398925065481956697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814111599283376987971131 4221167398925065481956697)
              ·
                refine ⟨3165875549193799111467523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4221167398925065481956697 3165875549193799111467523)
                ·
                  refine ⟨4748813323790698667201285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165875549193799111467523 4748813323790698667201285)
                  ·
                    refine ⟨890402498210756000100241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4748813323790698667201285 890402498210756000100241)
                    ·
                      rfl

theorem cell22_2601079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_2601079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601079 prefixEnd_2601079 := by exact prefixLift 2601079
  have htrace : WordTrace (prefixWord ++ tailWord_2601079) baseStart_2601079 baseEnd_2601079 := by
    simpa [prefixWord, tailWord_2601079, baseEnd_2601079] using wordTrace_append hprefix tailTrace_2601079
  have hstable : (prefixWord ++ tailWord_2601079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601079).length < 2 ^ (prefixWord ++ tailWord_2601079).sum := by decide
  have hdescent : baseEnd_2601079 < baseStart_2601079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601092 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2601092 : Nat := 118140960795 + 2601092 * 2 ^ 59
def prefixEnd_2601092 : Nat := 4983230072969 + 3 ^ 40 * 2601092 * 2
def baseEnd_2601092 : Nat := 890406948376428299525201

theorem tailTrace_2601092 : CollatzResearch.WordTrace tailWord_2601092 prefixEnd_2601092 890406948376428299525201 := by
  unfold tailWord_2601092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47434809546347694995830765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63246412728463593327774353 47434809546347694995830765)
  ·
    refine ⟨17788053579880385623436537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47434809546347694995830765 17788053579880385623436537)
    ·
      refine ⟨13341040184910289217577403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17788053579880385623436537 13341040184910289217577403)
      ·
        refine ⟨20011560277365433826366105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13341040184910289217577403 20011560277365433826366105)
        ·
          refine ⟨15008670208024075369774579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20011560277365433826366105 15008670208024075369774579)
          ·
            refine ⟨22513005312036113054661869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15008670208024075369774579 22513005312036113054661869)
            ·
              refine ⟨8442376992013542395498201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22513005312036113054661869 8442376992013542395498201)
              ·
                refine ⟨6331782744010156796623651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8442376992013542395498201 6331782744010156796623651)
                ·
                  refine ⟨9497674116015235194935477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6331782744010156796623651 9497674116015235194935477)
                  ·
                    refine ⟨890406948376428299525201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9497674116015235194935477 890406948376428299525201)
                    ·
                      rfl

theorem cell22_2601092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2601092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601092 prefixEnd_2601092 := by exact prefixLift 2601092
  have htrace : WordTrace (prefixWord ++ tailWord_2601092) baseStart_2601092 baseEnd_2601092 := by
    simpa [prefixWord, tailWord_2601092, baseEnd_2601092] using wordTrace_append hprefix tailTrace_2601092
  have hstable : (prefixWord ++ tailWord_2601092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601092).length < 2 ^ (prefixWord ++ tailWord_2601092).sum := by decide
  have hdescent : baseEnd_2601092 < baseStart_2601092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601096 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 1, 4]
def baseStart_2601096 : Nat := 118140960795 + 2601096 * 2 ^ 59
def prefixEnd_2601096 : Nat := 4983230072969 + 3 ^ 40 * 2601096 * 2
def baseEnd_2601096 : Nat := 890408317658173622425189

theorem tailTrace_2601096 : CollatzResearch.WordTrace tailWord_2601096 prefixEnd_2601096 890408317658173622425189 := by
  unfold tailWord_2601096
  simp only [CollatzResearch.WordTrace]
  refine ⟨47434882492340449337403571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63246509989787265783204761 47434882492340449337403571)
  ·
    refine ⟨71152323738510674006105357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47434882492340449337403571 71152323738510674006105357)
    ·
      refine ⟨26682121401941502752289509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71152323738510674006105357 26682121401941502752289509)
      ·
        refine ⟨5002897762864031766054283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26682121401941502752289509 5002897762864031766054283)
        ·
          refine ⟨7504346644296047649081425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5002897762864031766054283 7504346644296047649081425)
          ·
            refine ⟨5628259983222035736811069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7504346644296047649081425 5628259983222035736811069)
            ·
              refine ⟨2110597493708263401304151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5628259983222035736811069 2110597493708263401304151)
              ·
                refine ⟨3165896240562395101956227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110597493708263401304151 3165896240562395101956227)
                ·
                  refine ⟨4748844360843592652934341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165896240562395101956227 4748844360843592652934341)
                  ·
                    refine ⟨890408317658173622425189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4748844360843592652934341 890408317658173622425189)
                    ·
                      rfl

theorem cell22_2601096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_2601096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601096 prefixEnd_2601096 := by exact prefixLift 2601096
  have htrace : WordTrace (prefixWord ++ tailWord_2601096) baseStart_2601096 baseEnd_2601096 := by
    simpa [prefixWord, tailWord_2601096, baseEnd_2601096] using wordTrace_append hprefix tailTrace_2601096
  have hstable : (prefixWord ++ tailWord_2601096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601096).length < 2 ^ (prefixWord ++ tailWord_2601096).sum := by decide
  have hdescent : baseEnd_2601096 < baseStart_2601096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601109 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2601109 : Nat := 118140960795 + 2601109 * 2 ^ 59
def prefixEnd_2601109 : Nat := 4983230072969 + 3 ^ 40 * 2601109 * 2
def baseEnd_2601109 : Nat := 890412767823845921850149

theorem tailTrace_2601109 : CollatzResearch.WordTrace tailWord_2601109 prefixEnd_2601109 890412767823845921850149 := by
  unfold tailWord_2601109
  simp only [CollatzResearch.WordTrace]
  refine ⟨94870239133633801895030381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63246826089089201263353587 94870239133633801895030381)
  ·
    refine ⟨35576339675112675710636393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94870239133633801895030381 35576339675112675710636393)
    ·
      refine ⟨26682254756334506782977295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35576339675112675710636393 26682254756334506782977295)
      ·
        refine ⟨40023382134501760174465943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26682254756334506782977295 40023382134501760174465943)
        ·
          refine ⟨60035073201752640261698915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40023382134501760174465943 60035073201752640261698915)
          ·
            refine ⟨90052609802628960392548373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60035073201752640261698915 90052609802628960392548373)
            ·
              refine ⟨4221216084498232518400705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90052609802628960392548373 4221216084498232518400705)
              ·
                refine ⟨3165912063373674388800529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4221216084498232518400705 3165912063373674388800529)
                ·
                  refine ⟨2374434047530255791600397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165912063373674388800529 2374434047530255791600397)
                  ·
                    refine ⟨890412767823845921850149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374434047530255791600397 890412767823845921850149)
                    ·
                      rfl

theorem cell22_2601109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2601109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601109 prefixEnd_2601109 := by exact prefixLift 2601109
  have htrace : WordTrace (prefixWord ++ tailWord_2601109) baseStart_2601109 baseEnd_2601109 := by
    simpa [prefixWord, tailWord_2601109, baseEnd_2601109] using wordTrace_append hprefix tailTrace_2601109
  have hstable : (prefixWord ++ tailWord_2601109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601109).length < 2 ^ (prefixWord ++ tailWord_2601109).sum := by decide
  have hdescent : baseEnd_2601109 < baseStart_2601109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601135 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_2601135 : Nat := 118140960795 + 2601135 * 2 ^ 59
def prefixEnd_2601135 : Nat := 4983230072969 + 3 ^ 40 * 2601135 * 2
def baseEnd_2601135 : Nat := 890421668155190520700069

theorem tailTrace_2601135 : CollatzResearch.WordTrace tailWord_2601135 prefixEnd_2601135 890421668155190520700069 := by
  unfold tailWord_2601135
  simp only [CollatzResearch.WordTrace]
  refine ⟨94871187431539608335476859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63247458287693072223651239 94871187431539608335476859)
  ·
    refine ⟨142306781147309412503215289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94871187431539608335476859 142306781147309412503215289)
    ·
      refine ⟨106730085860482059377411467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142306781147309412503215289 106730085860482059377411467)
      ·
        refine ⟨160095128790723089066117201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106730085860482059377411467 160095128790723089066117201)
        ·
          refine ⟨120071346593042316799587901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160095128790723089066117201 120071346593042316799587901)
          ·
            refine ⟨45026754972390868799845463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120071346593042316799587901 45026754972390868799845463)
            ·
              refine ⟨67540132458586303199768195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45026754972390868799845463 67540132458586303199768195)
              ·
                refine ⟨101310198687879454799652293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67540132458586303199768195 101310198687879454799652293)
                ·
                  refine ⟨18995662253977397774934805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101310198687879454799652293 18995662253977397774934805)
                  ·
                    refine ⟨890421668155190520700069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18995662253977397774934805 890421668155190520700069)
                    ·
                      rfl

theorem cell22_2601135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_2601135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601135 prefixEnd_2601135 := by exact prefixLift 2601135
  have htrace : WordTrace (prefixWord ++ tailWord_2601135) baseStart_2601135 baseEnd_2601135 := by
    simpa [prefixWord, tailWord_2601135, baseEnd_2601135] using wordTrace_append hprefix tailTrace_2601135
  have hstable : (prefixWord ++ tailWord_2601135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601135).length < 2 ^ (prefixWord ++ tailWord_2601135).sum := by decide
  have hdescent : baseEnd_2601135 < baseStart_2601135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601184 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 5]
def baseStart_2601184 : Nat := 118140960795 + 2601184 * 2 ^ 59
def prefixEnd_2601184 : Nat := 4983230072969 + 3 ^ 40 * 2601184 * 2
def baseEnd_2601184 : Nat := 296812813952190242074973

theorem tailTrace_2601184 : CollatzResearch.WordTrace tailWord_2601184 prefixEnd_2601184 296812813952190242074973 := by
  unfold tailWord_2601184
  simp only [CollatzResearch.WordTrace]
  refine ⟨47436487304181044852005303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63248649738908059802673737 47436487304181044852005303)
  ·
    refine ⟨71154730956271567278007955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47436487304181044852005303 71154730956271567278007955)
    ·
      refine ⟨106732096434407350917011933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71154730956271567278007955 106732096434407350917011933)
      ·
        refine ⟨40024536162902756593879475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106732096434407350917011933 40024536162902756593879475)
        ·
          refine ⟨60036804244354134890819213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40024536162902756593879475 60036804244354134890819213)
          ·
            refine ⟨22513801591632800584057205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60036804244354134890819213 22513801591632800584057205)
            ·
              refine ⟨2110668899215575054755363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22513801591632800584057205 2110668899215575054755363)
              ·
                refine ⟨3166003348823362582133045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110668899215575054755363 3166003348823362582133045)
                ·
                  refine ⟨296812813952190242074973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3166003348823362582133045 296812813952190242074973)
                  ·
                    rfl

theorem cell22_2601184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_2601184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601184 prefixEnd_2601184 := by exact prefixLift 2601184
  have htrace : WordTrace (prefixWord ++ tailWord_2601184) baseStart_2601184 baseEnd_2601184 := by
    simpa [prefixWord, tailWord_2601184, baseEnd_2601184] using wordTrace_append hprefix tailTrace_2601184
  have hstable : (prefixWord ++ tailWord_2601184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601184).length < 2 ^ (prefixWord ++ tailWord_2601184).sum := by decide
  have hdescent : baseEnd_2601184 < baseStart_2601184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601278 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2601278 : Nat := 118140960795 + 2601278 * 2 ^ 59
def prefixEnd_2601278 : Nat := 4983230072969 + 3 ^ 40 * 2601278 * 2
def baseEnd_2601278 : Nat := 890470619977585814374631

theorem tailTrace_2601278 : CollatzResearch.WordTrace tailWord_2601278 prefixEnd_2601278 890470619977585814374631 := by
  unfold tailWord_2601278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11859550383752692969741561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63250935380014362505288325 11859550383752692969741561)
  ·
    refine ⟨8894662787814519727306171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11859550383752692969741561 8894662787814519727306171)
    ·
      refine ⟨13341994181721779590959257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8894662787814519727306171 13341994181721779590959257)
      ·
        refine ⟨10006495636291334693219443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13341994181721779590959257 10006495636291334693219443)
        ·
          refine ⟨15009743454437002039829165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006495636291334693219443 15009743454437002039829165)
          ·
            refine ⟨5628653795413875764935937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15009743454437002039829165 5628653795413875764935937)
            ·
              refine ⟨4221490346560406823701953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5628653795413875764935937 4221490346560406823701953)
              ·
                refine ⟨3166117759920305117776465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4221490346560406823701953 3166117759920305117776465)
                ·
                  refine ⟨2374588319940228838332349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3166117759920305117776465 2374588319940228838332349)
                  ·
                    refine ⟨890470619977585814374631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374588319940228838332349 890470619977585814374631)
                    ·
                      rfl

theorem cell22_2601278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2601278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601278 prefixEnd_2601278 := by exact prefixLift 2601278
  have htrace : WordTrace (prefixWord ++ tailWord_2601278) baseStart_2601278 baseEnd_2601278 := by
    simpa [prefixWord, tailWord_2601278, baseEnd_2601278] using wordTrace_append hprefix tailTrace_2601278
  have hstable : (prefixWord ++ tailWord_2601278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601278).length < 2 ^ (prefixWord ++ tailWord_2601278).sum := by decide
  have hdescent : baseEnd_2601278 < baseStart_2601278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601287 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2601287 : Nat := 118140960795 + 2601287 * 2 ^ 59
def prefixEnd_2601287 : Nat := 4983230072969 + 3 ^ 40 * 2601287 * 2
def baseEnd_2601287 : Nat := 890473700861512790899603

theorem tailTrace_2601287 : CollatzResearch.WordTrace tailWord_2601287 prefixEnd_2601287 890473700861512790899603 := by
  unfold tailWord_2601287
  simp only [CollatzResearch.WordTrace]
  refine ⟨94876731326988938295010115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63251154217992625530006743 94876731326988938295010115)
  ·
    refine ⟨142315096990483407442515173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94876731326988938295010115 142315096990483407442515173)
    ·
      refine ⟨26684080685715638895471595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142315096990483407442515173 26684080685715638895471595)
      ·
        refine ⟨40026121028573458343207393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26684080685715638895471595 40026121028573458343207393)
        ·
          refine ⟨30019590771430093757405545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40026121028573458343207393 30019590771430093757405545)
          ·
            refine ⟨22514693078572570318054159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30019590771430093757405545 22514693078572570318054159)
            ·
              refine ⟨33772039617858855477081239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22514693078572570318054159 33772039617858855477081239)
              ·
                refine ⟨50658059426788283215621859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33772039617858855477081239 50658059426788283215621859)
                ·
                  refine ⟨75987089140182424823432789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50658059426788283215621859 75987089140182424823432789)
                  ·
                    refine ⟨890473700861512790899603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75987089140182424823432789 890473700861512790899603)
                    ·
                      rfl

theorem cell22_2601287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2601287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601287 prefixEnd_2601287 := by exact prefixLift 2601287
  have htrace : WordTrace (prefixWord ++ tailWord_2601287) baseStart_2601287 baseEnd_2601287 := by
    simpa [prefixWord, tailWord_2601287, baseEnd_2601287] using wordTrace_append hprefix tailTrace_2601287
  have hstable : (prefixWord ++ tailWord_2601287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601287).length < 2 ^ (prefixWord ++ tailWord_2601287).sum := by decide
  have hdescent : baseEnd_2601287 < baseStart_2601287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601289 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_2601289 : Nat := 118140960795 + 2601289 * 2 ^ 59
def prefixEnd_2601289 : Nat := 4983230072969 + 3 ^ 40 * 2601289 * 2
def baseEnd_2601289 : Nat := 890474385502385452349597

theorem tailTrace_2601289 : CollatzResearch.WordTrace tailWord_2601289 prefixEnd_2601289 890474385502385452349597 := by
  unfold tailWord_2601289
  simp only [CollatzResearch.WordTrace]
  refine ⟨94876804272981692636582921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63251202848654461757721947 94876804272981692636582921)
  ·
    refine ⟨71157603204736269477437191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94876804272981692636582921 71157603204736269477437191)
    ·
      refine ⟨106736404807104404216155787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71157603204736269477437191 106736404807104404216155787)
      ·
        refine ⟨160104607210656606324233681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106736404807104404216155787 160104607210656606324233681)
        ·
          refine ⟨120078455407992454743175261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160104607210656606324233681 120078455407992454743175261)
          ·
            refine ⟨45029420777997170528690723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120078455407992454743175261 45029420777997170528690723)
            ·
              refine ⟨67544131166995755793036085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45029420777997170528690723 67544131166995755793036085)
              ·
                refine ⟨6332262296905852105597133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67544131166995755793036085 6332262296905852105597133)
                ·
                  refine ⟨2374598361339694539598925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6332262296905852105597133 2374598361339694539598925)
                  ·
                    refine ⟨890474385502385452349597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374598361339694539598925 890474385502385452349597)
                    ·
                      rfl

theorem cell22_2601289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_2601289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601289 prefixEnd_2601289 := by exact prefixLift 2601289
  have htrace : WordTrace (prefixWord ++ tailWord_2601289) baseStart_2601289 baseEnd_2601289 := by
    simpa [prefixWord, tailWord_2601289, baseEnd_2601289] using wordTrace_append hprefix tailTrace_2601289
  have hstable : (prefixWord ++ tailWord_2601289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601289).length < 2 ^ (prefixWord ++ tailWord_2601289).sum := by decide
  have hdescent : baseEnd_2601289 < baseStart_2601289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601308 : List Nat := [2, 2, 4, 3, 1, 1, 3, 6]
def baseStart_2601308 : Nat := 118140960795 + 2601308 * 2 ^ 59
def prefixEnd_2601308 : Nat := 4983230072969 + 3 ^ 40 * 2601308 * 2
def baseEnd_2601308 : Nat := 98942321065630637347171

theorem tailTrace_2601308 : CollatzResearch.WordTrace tailWord_2601308 prefixEnd_2601308 98942321065630637347171 := by
  unfold tailWord_2601308
  simp only [CollatzResearch.WordTrace]
  refine ⟨47438748629956429440762289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63251664839941905921016385 47438748629956429440762289)
  ·
    refine ⟨35579061472467322080571717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47438748629956429440762289 35579061472467322080571717)
    ·
      refine ⟨6671074026087622890107197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35579061472467322080571717 6671074026087622890107197)
      ·
        refine ⟨2501652759782858583790199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6671074026087622890107197 2501652759782858583790199)
        ·
          refine ⟨3752479139674287875685299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501652759782858583790199 3752479139674287875685299)
          ·
            refine ⟨5628718709511431813527949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752479139674287875685299 5628718709511431813527949)
            ·
              refine ⟨2110769516066786930072981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5628718709511431813527949 2110769516066786930072981)
              ·
                refine ⟨98942321065630637347171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2110769516066786930072981 98942321065630637347171)
                ·
                  rfl

theorem cell22_2601308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 6].length) (baseStart_2601308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601308 prefixEnd_2601308 := by exact prefixLift 2601308
  have htrace : WordTrace (prefixWord ++ tailWord_2601308) baseStart_2601308 baseEnd_2601308 := by
    simpa [prefixWord, tailWord_2601308, baseEnd_2601308] using wordTrace_append hprefix tailTrace_2601308
  have hstable : (prefixWord ++ tailWord_2601308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601308).length < 2 ^ (prefixWord ++ tailWord_2601308).sum := by decide
  have hdescent : baseEnd_2601308 < baseStart_2601308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601428 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2601428 : Nat := 118140960795 + 2601428 * 2 ^ 59
def prefixEnd_2601428 : Nat := 4983230072969 + 3 ^ 40 * 2601428 * 2
def baseEnd_2601428 : Nat := 890521968043035423124171

theorem tailTrace_2601428 : CollatzResearch.WordTrace tailWord_2601428 prefixEnd_2601428 890521968043035423124171 := by
  unfold tailWord_2601428
  simp only [CollatzResearch.WordTrace]
  refine ⟨47440937009739059687946469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63254582679652079583928625 47440937009739059687946469)
  ·
    refine ⟨8895175689326073691489963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47440937009739059687946469 8895175689326073691489963)
    ·
      refine ⟨13342763533989110537234945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895175689326073691489963 13342763533989110537234945)
      ·
        refine ⟨10007072650491832902926209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13342763533989110537234945 10007072650491832902926209)
        ·
          refine ⟨7505304487868874677194657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10007072650491832902926209 7505304487868874677194657)
          ·
            refine ⟨5628978365901656007895993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7505304487868874677194657 5628978365901656007895993)
            ·
              refine ⟨4221733774426242005921995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5628978365901656007895993 4221733774426242005921995)
              ·
                refine ⟨6332600661639363008882993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221733774426242005921995 6332600661639363008882993)
                ·
                  refine ⟨4749450496229522256662245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332600661639363008882993 4749450496229522256662245)
                  ·
                    refine ⟨890521968043035423124171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4749450496229522256662245 890521968043035423124171)
                    ·
                      rfl

theorem cell22_2601428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2601428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601428 prefixEnd_2601428 := by exact prefixLift 2601428
  have htrace : WordTrace (prefixWord ++ tailWord_2601428) baseStart_2601428 baseEnd_2601428 := by
    simpa [prefixWord, tailWord_2601428, baseEnd_2601428] using wordTrace_append hprefix tailTrace_2601428
  have hstable : (prefixWord ++ tailWord_2601428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601428).length < 2 ^ (prefixWord ++ tailWord_2601428).sum := by decide
  have hdescent : baseEnd_2601428 < baseStart_2601428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601492 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2601492 : Nat := 118140960795 + 2601492 * 2 ^ 59
def prefixEnd_2601492 : Nat := 4983230072969 + 3 ^ 40 * 2601492 * 2
def baseEnd_2601492 : Nat := 890543876550960589523975

theorem tailTrace_2601492 : CollatzResearch.WordTrace tailWord_2601492 prefixEnd_2601492 890543876550960589523975 := by
  unfold tailWord_2601492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47442104145623129153111365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63256138860830838870815153 47442104145623129153111365)
  ·
    refine ⟨8895394527304336716208381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47442104145623129153111365 8895394527304336716208381)
    ·
      refine ⟨3335772947739126268578143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8895394527304336716208381 3335772947739126268578143)
      ·
        refine ⟨5003659421608689402867215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3335772947739126268578143 5003659421608689402867215)
        ·
          refine ⟨7505489132413034104300823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5003659421608689402867215 7505489132413034104300823)
          ·
            refine ⟨11258233698619551156451235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505489132413034104300823 11258233698619551156451235)
            ·
              refine ⟨16887350547929326734676853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11258233698619551156451235 16887350547929326734676853)
              ·
                refine ⟨1583189113868374381375955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16887350547929326734676853 1583189113868374381375955)
                ·
                  refine ⟨2374783670802561572063933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583189113868374381375955 2374783670802561572063933)
                  ·
                    refine ⟨890543876550960589523975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374783670802561572063933 890543876550960589523975)
                    ·
                      rfl

theorem cell22_2601492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2601492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601492 prefixEnd_2601492 := by exact prefixLift 2601492
  have htrace : WordTrace (prefixWord ++ tailWord_2601492) baseStart_2601492 baseEnd_2601492 := by
    simpa [prefixWord, tailWord_2601492, baseEnd_2601492] using wordTrace_append hprefix tailTrace_2601492
  have hstable : (prefixWord ++ tailWord_2601492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601492).length < 2 ^ (prefixWord ++ tailWord_2601492).sum := by decide
  have hdescent : baseEnd_2601492 < baseStart_2601492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601546 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2601546 : Nat := 118140960795 + 2601546 * 2 ^ 59
def prefixEnd_2601546 : Nat := 4983230072969 + 3 ^ 40 * 2601546 * 2
def baseEnd_2601546 : Nat := 890562361854522448673809

theorem tailTrace_2601546 : CollatzResearch.WordTrace tailWord_2601546 prefixEnd_2601546 890562361854522448673809 := by
  unfold tailWord_2601546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23721544458262656382172123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63257451888700417019125661 23721544458262656382172123)
  ·
    refine ⟨35582316687393984573258185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23721544458262656382172123 35582316687393984573258185)
    ·
      refine ⟨26686737515545488429943639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35582316687393984573258185 26686737515545488429943639)
      ·
        refine ⟨40030106273318232644915459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26686737515545488429943639 40030106273318232644915459)
        ·
          refine ⟨60045159409977348967373189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40030106273318232644915459 60045159409977348967373189)
          ·
            refine ⟨11258467389370752931382473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60045159409977348967373189 11258467389370752931382473)
            ·
              refine ⟨8443850542028064698536855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11258467389370752931382473 8443850542028064698536855)
              ·
                refine ⟨12665775813042097047805283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8443850542028064698536855 12665775813042097047805283)
                ·
                  refine ⟨18998663719563145571707925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12665775813042097047805283 18998663719563145571707925)
                  ·
                    refine ⟨890562361854522448673809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18998663719563145571707925 890562361854522448673809)
                    ·
                      rfl

theorem cell22_2601546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2601546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601546 prefixEnd_2601546 := by exact prefixLift 2601546
  have htrace : WordTrace (prefixWord ++ tailWord_2601546) baseStart_2601546 baseEnd_2601546 := by
    simpa [prefixWord, tailWord_2601546, baseEnd_2601546] using wordTrace_append hprefix tailTrace_2601546
  have hstable : (prefixWord ++ tailWord_2601546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601546).length < 2 ^ (prefixWord ++ tailWord_2601546).sum := by decide
  have hdescent : baseEnd_2601546 < baseStart_2601546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601582 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_2601582 : Nat := 118140960795 + 2601582 * 2 ^ 59
def prefixEnd_2601582 : Nat := 4983230072969 + 3 ^ 40 * 2601582 * 2
def baseEnd_2601582 : Nat := 890574685390230354773699

theorem tailTrace_2601582 : CollatzResearch.WordTrace tailWord_2601582 prefixEnd_2601582 890574685390230354773699 := by
  unfold tailWord_2601582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11860936357615025459624875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63258327240613469117999333 11860936357615025459624875)
  ·
    refine ⟨17791404536422538189437313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11860936357615025459624875 17791404536422538189437313)
    ·
      refine ⟨13343553402316903642077985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17791404536422538189437313 13343553402316903642077985)
      ·
        refine ⟨10007665051737677731558489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13343553402316903642077985 10007665051737677731558489)
        ·
          refine ⟨7505748788803258298668867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10007665051737677731558489 7505748788803258298668867)
          ·
            refine ⟨11258623183204887448003301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505748788803258298668867 11258623183204887448003301)
            ·
              refine ⟨2110991846850916396500619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11258623183204887448003301 2110991846850916396500619)
              ·
                refine ⟨3166487770276374594750929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110991846850916396500619 3166487770276374594750929)
                ·
                  refine ⟨2374865827707280946063197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3166487770276374594750929 2374865827707280946063197)
                  ·
                    refine ⟨890574685390230354773699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374865827707280946063197 890574685390230354773699)
                    ·
                      rfl

theorem cell22_2601582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_2601582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601582 prefixEnd_2601582 := by exact prefixLift 2601582
  have htrace : WordTrace (prefixWord ++ tailWord_2601582) baseStart_2601582 baseEnd_2601582 := by
    simpa [prefixWord, tailWord_2601582, baseEnd_2601582] using wordTrace_append hprefix tailTrace_2601582
  have hstable : (prefixWord ++ tailWord_2601582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601582).length < 2 ^ (prefixWord ++ tailWord_2601582).sum := by decide
  have hdescent : baseEnd_2601582 < baseStart_2601582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601623 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 5]
def baseStart_2601623 : Nat := 118140960795 + 2601623 * 2 ^ 59
def prefixEnd_2601623 : Nat := 4983230072969 + 3 ^ 40 * 2601623 * 2
def baseEnd_2601623 : Nat := 296862906842706638166191

theorem tailTrace_2601623 : CollatzResearch.WordTrace tailWord_2601623 prefixEnd_2601623 296862906842706638166191 := by
  unfold tailWord_2601623
  simp only [CollatzResearch.WordTrace]
  refine ⟨94888986253771667679241523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63259324169181111786161015 94888986253771667679241523)
  ·
    refine ⟨142333479380657501518862285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94888986253771667679241523 142333479380657501518862285)
    ·
      refine ⟨53375054767746563069573357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142333479380657501518862285 53375054767746563069573357)
      ·
        refine ⟨20015645537904961151090009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53375054767746563069573357 20015645537904961151090009)
        ·
          refine ⟨15011734153428720863317507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20015645537904961151090009 15011734153428720863317507)
          ·
            refine ⟨22517601230143081294976261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15011734153428720863317507 22517601230143081294976261)
            ·
              refine ⟨4222050230651827742808049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22517601230143081294976261 4222050230651827742808049)
              ·
                refine ⟨3166537672988870807106037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4222050230651827742808049 3166537672988870807106037)
                ·
                  refine ⟨296862906842706638166191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3166537672988870807106037 296862906842706638166191)
                  ·
                    rfl

theorem cell22_2601623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 5].length) (baseStart_2601623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601623 prefixEnd_2601623 := by exact prefixLift 2601623
  have htrace : WordTrace (prefixWord ++ tailWord_2601623) baseStart_2601623 baseEnd_2601623 := by
    simpa [prefixWord, tailWord_2601623, baseEnd_2601623] using wordTrace_append hprefix tailTrace_2601623
  have hstable : (prefixWord ++ tailWord_2601623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601623).length < 2 ^ (prefixWord ++ tailWord_2601623).sum := by decide
  have hdescent : baseEnd_2601623 < baseStart_2601623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601651 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 8]
def baseStart_2601651 : Nat := 118140960795 + 2601651 * 2 ^ 59
def prefixEnd_2601651 : Nat := 4983230072969 + 3 ^ 40 * 2601651 * 2
def baseEnd_2601651 : Nat := 296866101833445724932829

theorem tailTrace_2601651 : CollatzResearch.WordTrace tailWord_2601651 prefixEnd_2601651 296866101833445724932829 := by
  unfold tailWord_2601651
  simp only [CollatzResearch.WordTrace]
  refine ⟨94890007497670228461260807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63260004998446818974173871 94890007497670228461260807)
  ·
    refine ⟨142335011246505342691891211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94890007497670228461260807 142335011246505342691891211)
    ·
      refine ⟨213502516869758014037836817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142335011246505342691891211 213502516869758014037836817)
      ·
        refine ⟨160126887652318510528377613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213502516869758014037836817 160126887652318510528377613)
        ·
          refine ⟨60047582869619441448141605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160126887652318510528377613 60047582869619441448141605)
          ·
            refine ⟨11258921788053645271526551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60047582869619441448141605 11258921788053645271526551)
            ·
              refine ⟨16888382682080467907289827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11258921788053645271526551 16888382682080467907289827)
              ·
                refine ⟨25332574023120701860934741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16888382682080467907289827 25332574023120701860934741)
                ·
                  refine ⟨296866101833445724932829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25332574023120701860934741 296866101833445724932829)
                  ·
                    rfl

theorem cell22_2601651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_2601651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601651 prefixEnd_2601651 := by exact prefixLift 2601651
  have htrace : WordTrace (prefixWord ++ tailWord_2601651) baseStart_2601651 baseEnd_2601651 := by
    simpa [prefixWord, tailWord_2601651, baseEnd_2601651] using wordTrace_append hprefix tailTrace_2601651
  have hstable : (prefixWord ++ tailWord_2601651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601651).length < 2 ^ (prefixWord ++ tailWord_2601651).sum := by decide
  have hdescent : baseEnd_2601651 < baseStart_2601651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601696 : List Nat := [2, 1, 1, 3, 1, 2, 1, 11]
def baseStart_2601696 : Nat := 118140960795 + 2601696 * 2 ^ 59
def prefixEnd_2601696 : Nat := 4983230072969 + 3 ^ 40 * 2601696 * 2
def baseEnd_2601696 : Nat := 98957078879996895269261

theorem tailTrace_2601696 : CollatzResearch.WordTrace tailWord_2601696 prefixEnd_2601696 98957078879996895269261 := by
  unfold tailWord_2601696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47445824391253600573324471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63261099188338134097765961 47445824391253600573324471)
  ·
    refine ⟨71168736586880400859986707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47445824391253600573324471 71168736586880400859986707)
    ·
      refine ⟨106753104880320601289980061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71168736586880400859986707 106753104880320601289980061)
      ·
        refine ⟨40032414330120225483742523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106753104880320601289980061 40032414330120225483742523)
        ·
          refine ⟨60048621495180338225613785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40032414330120225483742523 60048621495180338225613785)
          ·
            refine ⟨45036466121385253669210339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60048621495180338225613785 45036466121385253669210339)
            ·
              refine ⟨67554699182077880503815509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45036466121385253669210339 67554699182077880503815509)
              ·
                refine ⟨98957078879996895269261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67554699182077880503815509 98957078879996895269261)
                ·
                  rfl

theorem cell22_2601696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_2601696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601696 prefixEnd_2601696 := by exact prefixLift 2601696
  have htrace : WordTrace (prefixWord ++ tailWord_2601696) baseStart_2601696 baseEnd_2601696 := by
    simpa [prefixWord, tailWord_2601696, baseEnd_2601696] using wordTrace_append hprefix tailTrace_2601696
  have hstable : (prefixWord ++ tailWord_2601696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601696).length < 2 ^ (prefixWord ++ tailWord_2601696).sum := by decide
  have hdescent : baseEnd_2601696 < baseStart_2601696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601700 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_2601700 : Nat := 118140960795 + 2601700 * 2 ^ 59
def prefixEnd_2601700 : Nat := 4983230072969 + 3 ^ 40 * 2601700 * 2
def baseEnd_2601700 : Nat := 890615079201717380323337

theorem tailTrace_2601700 : CollatzResearch.WordTrace tailWord_2601700 prefixEnd_2601700 890615079201717380323337 := by
  unfold tailWord_2601700
  simp only [CollatzResearch.WordTrace]
  refine ⟨47445897337246354914897277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63261196449661806553196369 47445897337246354914897277)
  ·
    refine ⟨17792211501467383093086479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47445897337246354914897277 17792211501467383093086479)
    ·
      refine ⟨26688317252201074639629719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17792211501467383093086479 26688317252201074639629719)
      ·
        refine ⟨40032475878301611959444579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26688317252201074639629719 40032475878301611959444579)
        ·
          refine ⟨60048713817452417939166869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40032475878301611959444579 60048713817452417939166869)
          ·
            refine ⟨2814783460193082090898447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60048713817452417939166869 2814783460193082090898447)
            ·
              refine ⟨4222175190289623136347671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814783460193082090898447 4222175190289623136347671)
              ·
                refine ⟨6333262785434434704521507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222175190289623136347671 6333262785434434704521507)
                ·
                  refine ⟨9499894178151652056782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333262785434434704521507 9499894178151652056782261)
                  ·
                    refine ⟨890615079201717380323337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9499894178151652056782261 890615079201717380323337)
                    ·
                      rfl

theorem cell22_2601700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_2601700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601700 prefixEnd_2601700 := by exact prefixLift 2601700
  have htrace : WordTrace (prefixWord ++ tailWord_2601700) baseStart_2601700 baseEnd_2601700 := by
    simpa [prefixWord, tailWord_2601700, baseEnd_2601700] using wordTrace_append hprefix tailTrace_2601700
  have hstable : (prefixWord ++ tailWord_2601700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601700).length < 2 ^ (prefixWord ++ tailWord_2601700).sum := by decide
  have hdescent : baseEnd_2601700 < baseStart_2601700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601730 : List Nat := [3, 4, 1, 1, 1, 4, 8]
def baseStart_2601730 : Nat := 118140960795 + 2601730 * 2 ^ 59
def prefixEnd_2601730 : Nat := 4983230072969 + 3 ^ 40 * 2601730 * 2
def baseEnd_2601730 : Nat := 32986124030178048224935

theorem tailTrace_2601730 : CollatzResearch.WordTrace tailWord_2601730 prefixEnd_2601730 32986124030178048224935 := by
  unfold tailWord_2601730
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723222216096006238346661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63261925909589349968924429 23723222216096006238346661)
  ·
    refine ⟨4448104165518001169689999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23723222216096006238346661 4448104165518001169689999)
    ·
      refine ⟨6672156248277001754534999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448104165518001169689999 6672156248277001754534999)
      ·
        refine ⟨10008234372415502631802499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672156248277001754534999 10008234372415502631802499)
        ·
          refine ⟨15012351558623253947703749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10008234372415502631802499 15012351558623253947703749)
          ·
            refine ⟨2814815917241860115194453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15012351558623253947703749 2814815917241860115194453)
            ·
              refine ⟨32986124030178048224935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2814815917241860115194453 32986124030178048224935)
              ·
                rfl

theorem cell22_2601730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 8].length) (baseStart_2601730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601730 prefixEnd_2601730 := by exact prefixLift 2601730
  have htrace : WordTrace (prefixWord ++ tailWord_2601730) baseStart_2601730 baseEnd_2601730 := by
    simpa [prefixWord, tailWord_2601730, baseEnd_2601730] using wordTrace_append hprefix tailTrace_2601730
  have hstable : (prefixWord ++ tailWord_2601730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601730).length < 2 ^ (prefixWord ++ tailWord_2601730).sum := by decide
  have hdescent : baseEnd_2601730 < baseStart_2601730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601745 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_2601745 : Nat := 118140960795 + 2601745 * 2 ^ 59
def prefixEnd_2601745 : Nat := 4983230072969 + 3 ^ 40 * 2601745 * 2
def baseEnd_2601745 : Nat := 890630483621352262948199

theorem tailTrace_2601745 : CollatzResearch.WordTrace tailWord_2601745 prefixEnd_2601745 890630483621352262948199 := by
  unfold tailWord_2601745
  simp only [CollatzResearch.WordTrace]
  refine ⟨94893435959329682515182689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63262290639553121676788459 94893435959329682515182689)
  ·
    refine ⟨71170076969497261886387017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94893435959329682515182689 71170076969497261886387017)
    ·
      refine ⟨53377557727122946414790263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71170076969497261886387017 53377557727122946414790263)
      ·
        refine ⟨80066336590684419622185395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53377557727122946414790263 80066336590684419622185395)
        ·
          refine ⟨120099504886026629433278093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80066336590684419622185395 120099504886026629433278093)
          ·
            refine ⟨45037314332259986037479285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120099504886026629433278093 45037314332259986037479285)
            ·
              refine ⟨4222248218649373691013683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45037314332259986037479285 4222248218649373691013683)
              ·
                refine ⟨6333372327974060536520525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222248218649373691013683 6333372327974060536520525)
                ·
                  refine ⟨2375014622990272701195197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6333372327974060536520525 2375014622990272701195197)
                  ·
                    refine ⟨890630483621352262948199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375014622990272701195197 890630483621352262948199)
                    ·
                      rfl

theorem cell22_2601745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_2601745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601745 prefixEnd_2601745 := by exact prefixLift 2601745
  have htrace : WordTrace (prefixWord ++ tailWord_2601745) baseStart_2601745 baseEnd_2601745 := by
    simpa [prefixWord, tailWord_2601745, baseEnd_2601745] using wordTrace_append hprefix tailTrace_2601745
  have hstable : (prefixWord ++ tailWord_2601745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601745).length < 2 ^ (prefixWord ++ tailWord_2601745).sum := by decide
  have hdescent : baseEnd_2601745 < baseStart_2601745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601751 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 2, 3]
def baseStart_2601751 : Nat := 118140960795 + 2601751 * 2 ^ 59
def prefixEnd_2601751 : Nat := 4983230072969 + 3 ^ 40 * 2601751 * 2
def baseEnd_2601751 : Nat := 890632537543970247298181

theorem tailTrace_2601751 : CollatzResearch.WordTrace tailWord_2601751 prefixEnd_2601751 890632537543970247298181 := by
  unfold tailWord_2601751
  simp only [CollatzResearch.WordTrace]
  refine ⟨94893654797307945539901107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63262436531538630359934071 94893654797307945539901107)
  ·
    refine ⟨142340482195961918309851661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94893654797307945539901107 142340482195961918309851661)
    ·
      refine ⟨53377680823485719366194373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142340482195961918309851661 53377680823485719366194373)
      ·
        refine ⟨10008315154403572381161445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53377680823485719366194373 10008315154403572381161445)
        ·
          refine ⟨1876559091450669821467771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10008315154403572381161445 1876559091450669821467771)
          ·
            refine ⟨2814838637176004732201657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876559091450669821467771 2814838637176004732201657)
            ·
              refine ⟨2111128977882003549151243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814838637176004732201657 2111128977882003549151243)
              ·
                refine ⟨3166693466823005323726865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111128977882003549151243 3166693466823005323726865)
                ·
                  refine ⟨2375020100117253992795149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3166693466823005323726865 2375020100117253992795149)
                  ·
                    refine ⟨890632537543970247298181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375020100117253992795149 890632537543970247298181)
                    ·
                      rfl

theorem cell22_2601751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_2601751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601751 prefixEnd_2601751 := by exact prefixLift 2601751
  have htrace : WordTrace (prefixWord ++ tailWord_2601751) baseStart_2601751 baseEnd_2601751 := by
    simpa [prefixWord, tailWord_2601751, baseEnd_2601751] using wordTrace_append hprefix tailTrace_2601751
  have hstable : (prefixWord ++ tailWord_2601751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601751).length < 2 ^ (prefixWord ++ tailWord_2601751).sum := by decide
  have hdescent : baseEnd_2601751 < baseStart_2601751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601820 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_2601820 : Nat := 118140960795 + 2601820 * 2 ^ 59
def prefixEnd_2601820 : Nat := 4983230072969 + 3 ^ 40 * 2601820 * 2
def baseEnd_2601820 : Nat := 296885385884692355774323

theorem tailTrace_2601820 : CollatzResearch.WordTrace tailWord_2601820 prefixEnd_2601820 296885385884692355774323 := by
  unfold tailWord_2601820
  simp only [CollatzResearch.WordTrace]
  refine ⟨47448085717028985162081457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63264114289371980216108609 47448085717028985162081457)
  ·
    refine ⟨35586064287771738871561093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47448085717028985162081457 35586064287771738871561093)
    ·
      refine ⟨6672387053957201038417705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35586064287771738871561093 6672387053957201038417705)
      ·
        refine ⟨5004290290467900778813279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6672387053957201038417705 5004290290467900778813279)
        ·
          refine ⟨7506435435701851168219919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5004290290467900778813279 7506435435701851168219919)
          ·
            refine ⟨11259653153552776752329879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7506435435701851168219919 11259653153552776752329879)
            ·
              refine ⟨16889479730329165128494819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11259653153552776752329879 16889479730329165128494819)
              ·
                refine ⟨25334219595493747692742229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16889479730329165128494819 25334219595493747692742229)
                ·
                  refine ⟨296885385884692355774323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25334219595493747692742229 296885385884692355774323)
                  ·
                    rfl

theorem cell22_2601820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_2601820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601820 prefixEnd_2601820 := by exact prefixLift 2601820
  have htrace : WordTrace (prefixWord ++ tailWord_2601820) baseStart_2601820 baseEnd_2601820 := by
    simpa [prefixWord, tailWord_2601820, baseEnd_2601820] using wordTrace_append hprefix tailTrace_2601820
  have hstable : (prefixWord ++ tailWord_2601820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601820).length < 2 ^ (prefixWord ++ tailWord_2601820).sum := by decide
  have hdescent : baseEnd_2601820 < baseStart_2601820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601854 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2601854 : Nat := 118140960795 + 2601854 * 2 ^ 59
def prefixEnd_2601854 : Nat := 4983230072969 + 3 ^ 40 * 2601854 * 2
def baseEnd_2601854 : Nat := 296889265516304103990955

theorem tailTrace_2601854 : CollatzResearch.WordTrace tailWord_2601854 prefixEnd_2601854 296889265516304103990955 := by
  unfold tailWord_2601854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862176439491849266362577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63264941010623196087267077 11862176439491849266362577)
  ·
    refine ⟨8896632329618886949771933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11862176439491849266362577 8896632329618886949771933)
    ·
      refine ⟨3336237123607082606164475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8896632329618886949771933 3336237123607082606164475)
      ·
        refine ⟨5004355685410623909246713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336237123607082606164475 5004355685410623909246713)
        ·
          refine ⟨3753266764057967931935035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5004355685410623909246713 3753266764057967931935035)
          ·
            refine ⟨5629900146086951897902553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753266764057967931935035 5629900146086951897902553)
            ·
              refine ⟨4222425109565213923426915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5629900146086951897902553 4222425109565213923426915)
              ·
                refine ⟨6333637664347820885140373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222425109565213923426915 6333637664347820885140373)
                ·
                  refine ⟨296889265516304103990955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6333637664347820885140373 296889265516304103990955)
                  ·
                    rfl

theorem cell22_2601854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2601854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601854 prefixEnd_2601854 := by exact prefixLift 2601854
  have htrace : WordTrace (prefixWord ++ tailWord_2601854) baseStart_2601854 baseEnd_2601854 := by
    simpa [prefixWord, tailWord_2601854, baseEnd_2601854] using wordTrace_append hprefix tailTrace_2601854
  have hstable : (prefixWord ++ tailWord_2601854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601854).length < 2 ^ (prefixWord ++ tailWord_2601854).sum := by decide
  have hdescent : baseEnd_2601854 < baseStart_2601854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601927 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 5]
def baseStart_2601927 : Nat := 118140960795 + 2601927 * 2 ^ 59
def prefixEnd_2601927 : Nat := 4983230072969 + 3 ^ 40 * 2601927 * 2
def baseEnd_2601927 : Nat := 296897595313588151632547

theorem tailTrace_2601927 : CollatzResearch.WordTrace tailWord_2601927 prefixEnd_2601927 296897595313588151632547 := by
  unfold tailWord_2601927
  simp only [CollatzResearch.WordTrace]
  refine ⟨94900074044670327598308035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63266716029780218398872023 94900074044670327598308035)
  ·
    refine ⟨142350111067005491397462053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94900074044670327598308035 142350111067005491397462053)
    ·
      refine ⟨26690645825063529637024135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142350111067005491397462053 26690645825063529637024135)
      ·
        refine ⟨40035968737595294455536203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26690645825063529637024135 40035968737595294455536203)
        ·
          refine ⟨60053953106392941683304305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40035968737595294455536203 60053953106392941683304305)
          ·
            refine ⟨45040464829794706262478229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60053953106392941683304305 45040464829794706262478229)
            ·
              refine ⟨2111271788896626856053667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45040464829794706262478229 2111271788896626856053667)
              ·
                refine ⟨3166907683344940284080501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111271788896626856053667 3166907683344940284080501)
                ·
                  refine ⟨296897595313588151632547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3166907683344940284080501 296897595313588151632547)
                  ·
                    rfl

theorem cell22_2601927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 5].length) (baseStart_2601927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2601927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2601927 prefixEnd_2601927 := by exact prefixLift 2601927
  have htrace : WordTrace (prefixWord ++ tailWord_2601927) baseStart_2601927 baseEnd_2601927 := by
    simpa [prefixWord, tailWord_2601927, baseEnd_2601927] using wordTrace_append hprefix tailTrace_2601927
  have hstable : (prefixWord ++ tailWord_2601927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601927).length < 2 ^ (prefixWord ++ tailWord_2601927).sum := by decide
  have hdescent : baseEnd_2601927 < baseStart_2601927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602038 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2602038 : Nat := 118140960795 + 2602038 * 2 ^ 59
def prefixEnd_2602038 : Nat := 4983230072969 + 3 ^ 40 * 2602038 * 2
def baseEnd_2602038 : Nat := 890730783509197165372301

theorem tailTrace_2602038 : CollatzResearch.WordTrace tailWord_2602038 prefixEnd_2602038 890730783509197165372301 := by
  unfold tailWord_2602038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931507659204262097224923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63269415031512129037065845 5931507659204262097224923)
  ·
    refine ⟨8897261488806393145837385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5931507659204262097224923 8897261488806393145837385)
    ·
      refine ⟨6672946116604794859378039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8897261488806393145837385 6672946116604794859378039)
      ·
        refine ⟨10009419174907192289067059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672946116604794859378039 10009419174907192289067059)
        ·
          refine ⟨15014128762360788433600589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009419174907192289067059 15014128762360788433600589)
          ·
            refine ⟨5630298285885295662600221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15014128762360788433600589 5630298285885295662600221)
            ·
              refine ⟨2111361857206985873475083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5630298285885295662600221 2111361857206985873475083)
              ·
                refine ⟨3167042785810478810212625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111361857206985873475083 3167042785810478810212625)
                ·
                  refine ⟨2375282089357859107659469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167042785810478810212625 2375282089357859107659469)
                  ·
                    refine ⟨890730783509197165372301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375282089357859107659469 890730783509197165372301)
                    ·
                      rfl

theorem cell22_2602038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2602038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602038 prefixEnd_2602038 := by exact prefixLift 2602038
  have htrace : WordTrace (prefixWord ++ tailWord_2602038) baseStart_2602038 baseEnd_2602038 := by
    simpa [prefixWord, tailWord_2602038, baseEnd_2602038] using wordTrace_append hprefix tailTrace_2602038
  have hstable : (prefixWord ++ tailWord_2602038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602038).length < 2 ^ (prefixWord ++ tailWord_2602038).sum := by decide
  have hdescent : baseEnd_2602038 < baseStart_2602038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602092 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_2602092 : Nat := 118140960795 + 2602092 * 2 ^ 59
def prefixEnd_2602092 : Nat := 4983230072969 + 3 ^ 40 * 2602092 * 2
def baseEnd_2602092 : Nat := 890749268812759024522135

theorem tailTrace_2602092 : CollatzResearch.WordTrace tailWord_2602092 prefixEnd_2602092 890749268812759024522135 := by
  unfold tailWord_2602092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47453046044536280389032265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63270728059381707185376353 47453046044536280389032265)
  ·
    refine ⟨35589784533402210291774199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47453046044536280389032265 35589784533402210291774199)
    ·
      refine ⟨53384676800103315437661299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35589784533402210291774199 53384676800103315437661299)
      ·
        refine ⟨80077015200154973156491949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53384676800103315437661299 80077015200154973156491949)
        ·
          refine ⟨30028880700058114933684481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80077015200154973156491949 30028880700058114933684481)
          ·
            refine ⟨22521660525043586200263361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30028880700058114933684481 22521660525043586200263361)
            ·
              refine ⟨16891245393782689650197521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22521660525043586200263361 16891245393782689650197521)
              ·
                refine ⟨12668434045337017237648141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16891245393782689650197521 12668434045337017237648141)
                ·
                  refine ⟨4750662767001381464118053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12668434045337017237648141 4750662767001381464118053)
                  ·
                    refine ⟨890749268812759024522135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4750662767001381464118053 890749268812759024522135)
                    ·
                      rfl

theorem cell22_2602092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_2602092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602092 prefixEnd_2602092 := by exact prefixLift 2602092
  have htrace : WordTrace (prefixWord ++ tailWord_2602092) baseStart_2602092 baseEnd_2602092 := by
    simpa [prefixWord, tailWord_2602092, baseEnd_2602092] using wordTrace_append hprefix tailTrace_2602092
  have hstable : (prefixWord ++ tailWord_2602092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602092).length < 2 ^ (prefixWord ++ tailWord_2602092).sum := by decide
  have hdescent : baseEnd_2602092 < baseStart_2602092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602169 : List Nat := [1, 2, 1, 4, 1, 4, 3, 6]
def baseStart_2602169 : Nat := 118140960795 + 2602169 * 2 ^ 59
def prefixEnd_2602169 : Nat := 4983230072969 + 3 ^ 40 * 2602169 * 2
def baseEnd_2602169 : Nat := 98975069720706276705211

theorem tailTrace_2602169 : CollatzResearch.WordTrace tailWord_2602169 prefixEnd_2602169 98975069720706276705211 := by
  unfold tailWord_2602169
  simp only [CollatzResearch.WordTrace]
  refine ⟨94908900509793602928617561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63272600339862401952411707 94908900509793602928617561)
  ·
    refine ⟨71181675382345202196463171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94908900509793602928617561 71181675382345202196463171)
    ·
      refine ⟨106772513073517803294694757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71181675382345202196463171 106772513073517803294694757)
      ·
        refine ⟨20019846201284588117755267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106772513073517803294694757 20019846201284588117755267)
        ·
          refine ⟨30029769301926882176632901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20019846201284588117755267 30029769301926882176632901)
          ·
            refine ⟨5630581744111290408118669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30029769301926882176632901 5630581744111290408118669)
            ·
              refine ⟨2111468154041733903044501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5630581744111290408118669 2111468154041733903044501)
              ·
                refine ⟨98975069720706276705211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2111468154041733903044501 98975069720706276705211)
                ·
                  rfl

theorem cell22_2602169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 6].length) (baseStart_2602169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602169 prefixEnd_2602169 := by exact prefixLift 2602169
  have htrace : WordTrace (prefixWord ++ tailWord_2602169) baseStart_2602169 baseEnd_2602169 := by
    simpa [prefixWord, tailWord_2602169, baseEnd_2602169] using wordTrace_append hprefix tailTrace_2602169
  have hstable : (prefixWord ++ tailWord_2602169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602169).length < 2 ^ (prefixWord ++ tailWord_2602169).sum := by decide
  have hdescent : baseEnd_2602169 < baseStart_2602169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602190 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_2602190 : Nat := 118140960795 + 2602190 * 2 ^ 59
def prefixEnd_2602190 : Nat := 4983230072969 + 3 ^ 40 * 2602190 * 2
def baseEnd_2602190 : Nat := 890782816215519435571835

theorem tailTrace_2602190 : CollatzResearch.WordTrace tailWord_2602190 prefixEnd_2602190 890782816215519435571835 := by
  unfold tailWord_2602190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11863708305339690439391503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63273110961811682343421349 11863708305339690439391503)
  ·
    refine ⟨17795562458009535659087255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11863708305339690439391503 17795562458009535659087255)
    ·
      refine ⟨26693343687014303488630883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17795562458009535659087255 26693343687014303488630883)
      ·
        refine ⟨40040015530521455232946325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26693343687014303488630883 40040015530521455232946325)
        ·
          refine ⟨1876875727993193214044359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40040015530521455232946325 1876875727993193214044359)
          ·
            refine ⟨2815313591989789821066539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876875727993193214044359 2815313591989789821066539)
            ·
              refine ⟨4222970387984684731599809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815313591989789821066539 4222970387984684731599809)
              ·
                refine ⟨3167227790988513548699857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4222970387984684731599809 3167227790988513548699857)
                ·
                  refine ⟨2375420843241385161524893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167227790988513548699857 2375420843241385161524893)
                  ·
                    refine ⟨890782816215519435571835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375420843241385161524893 890782816215519435571835)
                    ·
                      rfl

theorem cell22_2602190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_2602190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602190 prefixEnd_2602190 := by exact prefixLift 2602190
  have htrace : WordTrace (prefixWord ++ tailWord_2602190) baseStart_2602190 baseEnd_2602190 := by
    simpa [prefixWord, tailWord_2602190, baseEnd_2602190] using wordTrace_append hprefix tailTrace_2602190
  have hstable : (prefixWord ++ tailWord_2602190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602190).length < 2 ^ (prefixWord ++ tailWord_2602190).sum := by decide
  have hdescent : baseEnd_2602190 < baseStart_2602190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602336 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_2602336 : Nat := 118140960795 + 2602336 * 2 ^ 59
def prefixEnd_2602336 : Nat := 4983230072969 + 3 ^ 40 * 2602336 * 2
def baseEnd_2602336 : Nat := 890832794999223721421387

theorem tailTrace_2602336 : CollatzResearch.WordTrace tailWord_2602336 prefixEnd_2602336 890832794999223721421387 := by
  unfold tailWord_2602336
  simp only [CollatzResearch.WordTrace]
  refine ⟨47457495750094295224973431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63276661000125726966631241 47457495750094295224973431)
  ·
    refine ⟨71186243625141442837460147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47457495750094295224973431 71186243625141442837460147)
    ·
      refine ⟨106779365437712164256190221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71186243625141442837460147 106779365437712164256190221)
      ·
        refine ⟨40042262039142061596071333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106779365437712164256190221 40042262039142061596071333)
        ·
          refine ⟨7507924132339136549263375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40042262039142061596071333 7507924132339136549263375)
          ·
            refine ⟨11261886198508704823895063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507924132339136549263375 11261886198508704823895063)
            ·
              refine ⟨16892829297763057235842595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11261886198508704823895063 16892829297763057235842595)
              ·
                refine ⟨25339243946644585853763893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16892829297763057235842595 25339243946644585853763893)
                ·
                  refine ⟨2375554119997929923790365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25339243946644585853763893 2375554119997929923790365)
                  ·
                    refine ⟨890832794999223721421387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375554119997929923790365 890832794999223721421387)
                    ·
                      rfl

theorem cell22_2602336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_2602336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602336 prefixEnd_2602336 := by exact prefixLift 2602336
  have htrace : WordTrace (prefixWord ++ tailWord_2602336) baseStart_2602336 baseEnd_2602336 := by
    simpa [prefixWord, tailWord_2602336, baseEnd_2602336] using wordTrace_append hprefix tailTrace_2602336
  have hstable : (prefixWord ++ tailWord_2602336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602336).length < 2 ^ (prefixWord ++ tailWord_2602336).sum := by decide
  have hdescent : baseEnd_2602336 < baseStart_2602336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602353 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 1, 3]
def baseStart_2602353 : Nat := 118140960795 + 2602353 * 2 ^ 59
def prefixEnd_2602353 : Nat := 4983230072969 + 3 ^ 40 * 2602353 * 2
def baseEnd_2602353 : Nat := 890838614446641343746335

theorem tailTrace_2602353 : CollatzResearch.WordTrace tailWord_2602353 prefixEnd_2602353 890838614446641343746335 := by
  unfold tailWord_2602353
  simp only [CollatzResearch.WordTrace]
  refine ⟨94915611541127002353315713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63277074360751334902210475 94915611541127002353315713)
  ·
    refine ⟨71186708655845251764986785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94915611541127002353315713 71186708655845251764986785)
    ·
      refine ⟨53390031491883938823740089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71186708655845251764986785 53390031491883938823740089)
      ·
        refine ⟨40042523618912954117805067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53390031491883938823740089 40042523618912954117805067)
        ·
          refine ⟨60063785428369431176707601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40042523618912954117805067 60063785428369431176707601)
          ·
            refine ⟨45047839071277073382530701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60063785428369431176707601 45047839071277073382530701)
            ·
              refine ⟨16892939651728902518449013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45047839071277073382530701 16892939651728902518449013)
              ·
                refine ⟨1583713092349584611104595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16892939651728902518449013 1583713092349584611104595)
                ·
                  refine ⟨2375569638524376916656893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583713092349584611104595 2375569638524376916656893)
                  ·
                    refine ⟨890838614446641343746335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375569638524376916656893 890838614446641343746335)
                    ·
                      rfl

theorem cell22_2602353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_2602353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602353 prefixEnd_2602353 := by exact prefixLift 2602353
  have htrace : WordTrace (prefixWord ++ tailWord_2602353) baseStart_2602353 baseEnd_2602353 := by
    simpa [prefixWord, tailWord_2602353, baseEnd_2602353] using wordTrace_append hprefix tailTrace_2602353
  have hstable : (prefixWord ++ tailWord_2602353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602353).length < 2 ^ (prefixWord ++ tailWord_2602353).sum := by decide
  have hdescent : baseEnd_2602353 < baseStart_2602353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602364 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_2602364 : Nat := 118140960795 + 2602364 * 2 ^ 59
def prefixEnd_2602364 : Nat := 4983230072969 + 3 ^ 40 * 2602364 * 2
def baseEnd_2602364 : Nat := 890842379971440981721301

theorem tailTrace_2602364 : CollatzResearch.WordTrace tailWord_2602364 prefixEnd_2602364 890842379971440981721301 := by
  unfold tailWord_2602364
  simp only [CollatzResearch.WordTrace]
  refine ⟨47458006372043575615983073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63277341829391434154644097 47458006372043575615983073)
  ·
    refine ⟨35593504779032681711987305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47458006372043575615983073 35593504779032681711987305)
    ·
      refine ⟨26695128584274511283990479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35593504779032681711987305 26695128584274511283990479)
      ·
        refine ⟨40042692876411766925985719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26695128584274511283990479 40042692876411766925985719)
        ·
          refine ⟨60064039314617650388978579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40042692876411766925985719 60064039314617650388978579)
          ·
            refine ⟨90096058971926475583467869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60064039314617650388978579 90096058971926475583467869)
            ·
              refine ⟨33786022114472428343800451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90096058971926475583467869 33786022114472428343800451)
              ·
                refine ⟨50679033171708642515700677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33786022114472428343800451 50679033171708642515700677)
                ·
                  refine ⟨9502318719695370471693877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50679033171708642515700677 9502318719695370471693877)
                  ·
                    refine ⟨890842379971440981721301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9502318719695370471693877 890842379971440981721301)
                    ·
                      rfl

theorem cell22_2602364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_2602364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602364 prefixEnd_2602364 := by exact prefixLift 2602364
  have htrace : WordTrace (prefixWord ++ tailWord_2602364) baseStart_2602364 baseEnd_2602364 := by
    simpa [prefixWord, tailWord_2602364, baseEnd_2602364] using wordTrace_append hprefix tailTrace_2602364
  have hstable : (prefixWord ++ tailWord_2602364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602364).length < 2 ^ (prefixWord ++ tailWord_2602364).sum := by decide
  have hdescent : baseEnd_2602364 < baseStart_2602364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602370 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2602370 : Nat := 118140960795 + 2602370 * 2 ^ 59
def prefixEnd_2602370 : Nat := 4983230072969 + 3 ^ 40 * 2602370 * 2
def baseEnd_2602370 : Nat := 890844433894058966071283

theorem tailTrace_2602370 : CollatzResearch.WordTrace tailWord_2602370 prefixEnd_2602370 890844433894058966071283 := by
  unfold tailWord_2602370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729057895516353564171141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63277487721376942837789709 23729057895516353564171141)
  ·
    refine ⟨4449198355409316293282089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23729057895516353564171141 4449198355409316293282089)
    ·
      refine ⟨3336898766556987219961567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4449198355409316293282089 3336898766556987219961567)
      ·
        refine ⟨5005348149835480829942351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336898766556987219961567 5005348149835480829942351)
        ·
          refine ⟨7508022224753221244913527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005348149835480829942351 7508022224753221244913527)
          ·
            refine ⟨11262033337129831867370291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7508022224753221244913527 11262033337129831867370291)
            ·
              refine ⟨16893050005694747801055437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262033337129831867370291 16893050005694747801055437)
              ·
                refine ⟨6334893752135530425395789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16893050005694747801055437 6334893752135530425395789)
                ·
                  refine ⟨2375585157050823909523421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6334893752135530425395789 2375585157050823909523421)
                  ·
                    refine ⟨890844433894058966071283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375585157050823909523421 890844433894058966071283)
                    ·
                      rfl

theorem cell22_2602370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2602370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602370 prefixEnd_2602370 := by exact prefixLift 2602370
  have htrace : WordTrace (prefixWord ++ tailWord_2602370) baseStart_2602370 baseEnd_2602370 := by
    simpa [prefixWord, tailWord_2602370, baseEnd_2602370] using wordTrace_append hprefix tailTrace_2602370
  have hstable : (prefixWord ++ tailWord_2602370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602370).length < 2 ^ (prefixWord ++ tailWord_2602370).sum := by decide
  have hdescent : baseEnd_2602370 < baseStart_2602370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602434 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2602434 : Nat := 118140960795 + 2602434 * 2 ^ 59
def prefixEnd_2602434 : Nat := 4983230072969 + 3 ^ 40 * 2602434 * 2
def baseEnd_2602434 : Nat := 296955447467328044157029

theorem tailTrace_2602434 : CollatzResearch.WordTrace tailWord_2602434 prefixEnd_2602434 296955447467328044157029 := by
  unfold tailWord_2602434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729641463458388296753589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63279043902555702124676237 23729641463458388296753589)
  ·
    refine ⟨2224653887199223902820649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23729641463458388296753589 2224653887199223902820649)
    ·
      refine ⟨1668490415399417927115487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2224653887199223902820649 1668490415399417927115487)
      ·
        refine ⟨2502735623099126890673231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668490415399417927115487 2502735623099126890673231)
        ·
          refine ⟨3754103434648690336009847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502735623099126890673231 3754103434648690336009847)
          ·
            refine ⟨5631155151973035504014771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754103434648690336009847 5631155151973035504014771)
            ·
              refine ⟨8446732727959553256022157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631155151973035504014771 8446732727959553256022157)
              ·
                refine ⟨3167524772984832471008309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8446732727959553256022157 3167524772984832471008309)
                ·
                  refine ⟨296955447467328044157029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3167524772984832471008309 296955447467328044157029)
                  ·
                    rfl

theorem cell22_2602434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2602434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602434 prefixEnd_2602434 := by exact prefixLift 2602434
  have htrace : WordTrace (prefixWord ++ tailWord_2602434) baseStart_2602434 baseEnd_2602434 := by
    simpa [prefixWord, tailWord_2602434, baseEnd_2602434] using wordTrace_append hprefix tailTrace_2602434
  have hstable : (prefixWord ++ tailWord_2602434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602434).length < 2 ^ (prefixWord ++ tailWord_2602434).sum := by decide
  have hdescent : baseEnd_2602434 < baseStart_2602434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602458 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_2602458 : Nat := 118140960795 + 2602458 * 2 ^ 59
def prefixEnd_2602458 : Nat := 4983230072969 + 3 ^ 40 * 2602458 * 2
def baseEnd_2602458 : Nat := 890874558092456069871013

theorem tailTrace_2602458 : CollatzResearch.WordTrace tailWord_2602458 prefixEnd_2602458 890874558092456069871013 := by
  unfold tailWord_2602458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729860301436651321472007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63279627470497736857258685 23729860301436651321472007)
  ·
    refine ⟨35594790452154976982208011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23729860301436651321472007 35594790452154976982208011)
    ·
      refine ⟨53392185678232465473312017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35594790452154976982208011 53392185678232465473312017)
      ·
        refine ⟨40044139258674349104984013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53392185678232465473312017 40044139258674349104984013)
        ·
          refine ⟨15016552222002880914369005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40044139258674349104984013 15016552222002880914369005)
          ·
            refine ⟨5631207083251080342888377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15016552222002880914369005 5631207083251080342888377)
            ·
              refine ⟨4223405312438310257166283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5631207083251080342888377 4223405312438310257166283)
              ·
                refine ⟨6335107968657465385749425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223405312438310257166283 6335107968657465385749425)
                ·
                  refine ⟨4751330976493099039312069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335107968657465385749425 4751330976493099039312069)
                  ·
                    refine ⟨890874558092456069871013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751330976493099039312069 890874558092456069871013)
                    ·
                      rfl

theorem cell22_2602458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_2602458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602458 prefixEnd_2602458 := by exact prefixLift 2602458
  have htrace : WordTrace (prefixWord ++ tailWord_2602458) baseStart_2602458 baseEnd_2602458 := by
    simpa [prefixWord, tailWord_2602458, baseEnd_2602458] using wordTrace_append hprefix tailTrace_2602458
  have hstable : (prefixWord ++ tailWord_2602458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602458).length < 2 ^ (prefixWord ++ tailWord_2602458).sum := by decide
  have hdescent : baseEnd_2602458 < baseStart_2602458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602477 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2602477 : Nat := 118140960795 + 2602477 * 2 ^ 59
def prefixEnd_2602477 : Nat := 4983230072969 + 3 ^ 40 * 2602477 * 2
def baseEnd_2602477 : Nat := 890881062180746353645955

theorem tailTrace_2602477 : CollatzResearch.WordTrace tailWord_2602477 prefixEnd_2602477 890881062180746353645955 := by
  unfold tailWord_2602477
  simp only [CollatzResearch.WordTrace]
  refine ⟨94920134192677771530829685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63280089461785181020553123 94920134192677771530829685)
  ·
    refine ⟨8898762580563541081015283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94920134192677771530829685 8898762580563541081015283)
    ·
      refine ⟨13348143870845311621522925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8898762580563541081015283 13348143870845311621522925)
      ·
        refine ⟨5005553951566991858071097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13348143870845311621522925 5005553951566991858071097)
        ·
          refine ⟨3754165463675243893553323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5005553951566991858071097 3754165463675243893553323)
          ·
            refine ⟨5631248195512865840329985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754165463675243893553323 5631248195512865840329985)
            ·
              refine ⟨4223436146634649380247489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5631248195512865840329985 4223436146634649380247489)
              ·
                refine ⟨3167577109975987035185617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4223436146634649380247489 3167577109975987035185617)
                ·
                  refine ⟨2375682832481990276389213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167577109975987035185617 2375682832481990276389213)
                  ·
                    refine ⟨890881062180746353645955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375682832481990276389213 890881062180746353645955)
                    ·
                      rfl

theorem cell22_2602477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2602477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602477 prefixEnd_2602477 := by exact prefixLift 2602477
  have htrace : WordTrace (prefixWord ++ tailWord_2602477) baseStart_2602477 baseEnd_2602477 := by
    simpa [prefixWord, tailWord_2602477, baseEnd_2602477] using wordTrace_append hprefix tailTrace_2602477
  have hstable : (prefixWord ++ tailWord_2602477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602477).length < 2 ^ (prefixWord ++ tailWord_2602477).sum := by decide
  have hdescent : baseEnd_2602477 < baseStart_2602477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602509 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2602509 : Nat := 118140960795 + 2602509 * 2 ^ 59
def prefixEnd_2602509 : Nat := 4983230072969 + 3 ^ 40 * 2602509 * 2
def baseEnd_2602509 : Nat := 890892016434708936845857

theorem tailTrace_2602509 : CollatzResearch.WordTrace tailWord_2602509 prefixEnd_2602509 890892016434708936845857 := by
  unfold tailWord_2602509
  simp only [CollatzResearch.WordTrace]
  refine ⟨94921301328561840995994581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63280867552374560663996387 94921301328561840995994581)
  ·
    refine ⟨2224717999888168148343623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 94921301328561840995994581 2224717999888168148343623)
    ·
      refine ⟨3337076999832252222515435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224717999888168148343623 3337076999832252222515435)
      ·
        refine ⟨5005615499748378333773153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337076999832252222515435 5005615499748378333773153)
        ·
          refine ⟨3754211624811283750329865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5005615499748378333773153 3754211624811283750329865)
          ·
            refine ⟨2815658718608462812747399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3754211624811283750329865 2815658718608462812747399)
            ·
              refine ⟨4223488077912694219121099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815658718608462812747399 4223488077912694219121099)
              ·
                refine ⟨6335232116869041328681649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223488077912694219121099 6335232116869041328681649)
                ·
                  refine ⟨4751424087651780996511237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335232116869041328681649 4751424087651780996511237)
                  ·
                    refine ⟨890892016434708936845857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751424087651780996511237 890892016434708936845857)
                    ·
                      rfl

theorem cell22_2602509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2602509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602509 prefixEnd_2602509 := by exact prefixLift 2602509
  have htrace : WordTrace (prefixWord ++ tailWord_2602509) baseStart_2602509 baseEnd_2602509 := by
    simpa [prefixWord, tailWord_2602509, baseEnd_2602509] using wordTrace_append hprefix tailTrace_2602509
  have hstable : (prefixWord ++ tailWord_2602509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602509).length < 2 ^ (prefixWord ++ tailWord_2602509).sum := by decide
  have hdescent : baseEnd_2602509 < baseStart_2602509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602576 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_2602576 : Nat := 118140960795 + 2602576 * 2 ^ 59
def prefixEnd_2602576 : Nat := 4983230072969 + 3 ^ 40 * 2602576 * 2
def baseEnd_2602576 : Nat := 890914951903943095420651

theorem tailTrace_2602576 : CollatzResearch.WordTrace tailWord_2602576 prefixEnd_2602576 890914951903943095420651 := by
  unfold tailWord_2602576
  simp only [CollatzResearch.WordTrace]
  refine ⟨47461872509659555719341791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63282496679546074292455721 47461872509659555719341791)
  ·
    refine ⟨71192808764489333579012687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47461872509659555719341791 71192808764489333579012687)
    ·
      refine ⟨106789213146734000368519031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71192808764489333579012687 106789213146734000368519031)
      ·
        refine ⟨160183819720101000552778547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106789213146734000368519031 160183819720101000552778547)
        ·
          refine ⟨240275729580151500829167821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160183819720101000552778547 240275729580151500829167821)
          ·
            refine ⟨90103398592556812810937933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240275729580151500829167821 90103398592556812810937933)
            ·
              refine ⟨33788774472208804804101725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90103398592556812810937933 33788774472208804804101725)
              ·
                refine ⟨12670790427078301801538147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33788774472208804804101725 12670790427078301801538147)
                ·
                  refine ⟨19006185640617452702307221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12670790427078301801538147 19006185640617452702307221)
                  ·
                    refine ⟨890914951903943095420651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19006185640617452702307221 890914951903943095420651)
                    ·
                      rfl

theorem cell22_2602576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_2602576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602576 prefixEnd_2602576 := by exact prefixLift 2602576
  have htrace : WordTrace (prefixWord ++ tailWord_2602576) baseStart_2602576 baseEnd_2602576 := by
    simpa [prefixWord, tailWord_2602576, baseEnd_2602576] using wordTrace_append hprefix tailTrace_2602576
  have hstable : (prefixWord ++ tailWord_2602576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602576).length < 2 ^ (prefixWord ++ tailWord_2602576).sum := by decide
  have hdescent : baseEnd_2602576 < baseStart_2602576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602593 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2602593 : Nat := 118140960795 + 2602593 * 2 ^ 59
def prefixEnd_2602593 : Nat := 4983230072969 + 3 ^ 40 * 2602593 * 2
def baseEnd_2602593 : Nat := 890920771351360717745599

theorem tailTrace_2602593 : CollatzResearch.WordTrace tailWord_2602593 prefixEnd_2602593 890920771351360717745599 := by
  unfold tailWord_2602593
  simp only [CollatzResearch.WordTrace]
  refine ⟨94924365060257523342052433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63282910040171682228034955 94924365060257523342052433)
  ·
    refine ⟨71193273795193142506539325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94924365060257523342052433 71193273795193142506539325)
    ·
      refine ⟨26697477673197428439952247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71193273795193142506539325 26697477673197428439952247)
      ·
        refine ⟨40046216509796142659928371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26697477673197428439952247 40046216509796142659928371)
        ·
          refine ⟨60069324764694213989892557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40046216509796142659928371 60069324764694213989892557)
          ·
            refine ⟨22525996786760330246209709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60069324764694213989892557 22525996786760330246209709)
            ·
              refine ⟨8447248795035123842328641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22525996786760330246209709 8447248795035123842328641)
              ·
                refine ⟨6335436596276342881746481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8447248795035123842328641 6335436596276342881746481)
                ·
                  refine ⟨4751577447207257161309861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335436596276342881746481 4751577447207257161309861)
                  ·
                    refine ⟨890920771351360717745599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4751577447207257161309861 890920771351360717745599)
                    ·
                      rfl

theorem cell22_2602593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2602593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602593 prefixEnd_2602593 := by exact prefixLift 2602593
  have htrace : WordTrace (prefixWord ++ tailWord_2602593) baseStart_2602593 baseEnd_2602593 := by
    simpa [prefixWord, tailWord_2602593, baseEnd_2602593] using wordTrace_append hprefix tailTrace_2602593
  have hstable : (prefixWord ++ tailWord_2602593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602593).length < 2 ^ (prefixWord ++ tailWord_2602593).sum := by decide
  have hdescent : baseEnd_2602593 < baseStart_2602593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602597 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 4]
def baseStart_2602597 : Nat := 118140960795 + 2602597 * 2 ^ 59
def prefixEnd_2602597 : Nat := 4983230072969 + 3 ^ 40 * 2602597 * 2
def baseEnd_2602597 : Nat := 296974046877702013548529

theorem tailTrace_2602597 : CollatzResearch.WordTrace tailWord_2602597 prefixEnd_2602597 296974046877702013548529 := by
  unfold tailWord_2602597
  simp only [CollatzResearch.WordTrace]
  refine ⟨94924510952243032025198045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63283007301495354683465363 94924510952243032025198045)
  ·
    refine ⟨35596691607091137009449267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94924510952243032025198045 35596691607091137009449267)
    ·
      refine ⟨53395037410636705514173901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35596691607091137009449267 53395037410636705514173901)
      ·
        refine ⟨20023139028988764567815213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53395037410636705514173901 20023139028988764567815213)
        ·
          refine ⟨7508677135870786712930705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20023139028988764567815213 7508677135870786712930705)
          ·
            refine ⟨5631507851903090034698029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7508677135870786712930705 5631507851903090034698029)
            ·
              refine ⟨2111815444463658763011761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5631507851903090034698029 2111815444463658763011761)
              ·
                refine ⟨1583861583347744072258821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111815444463658763011761 1583861583347744072258821)
                ·
                  refine ⟨296974046877702013548529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583861583347744072258821 296974046877702013548529)
                  ·
                    rfl

theorem cell22_2602597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_2602597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602597 prefixEnd_2602597 := by exact prefixLift 2602597
  have htrace : WordTrace (prefixWord ++ tailWord_2602597) baseStart_2602597 baseEnd_2602597 := by
    simpa [prefixWord, tailWord_2602597, baseEnd_2602597] using wordTrace_append hprefix tailTrace_2602597
  have hstable : (prefixWord ++ tailWord_2602597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602597).length < 2 ^ (prefixWord ++ tailWord_2602597).sum := by decide
  have hdescent : baseEnd_2602597 < baseStart_2602597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602608 : List Nat := [2, 1, 1, 1, 6, 2, 2, 7]
def baseStart_2602608 : Nat := 118140960795 + 2602608 * 2 ^ 59
def prefixEnd_2602608 : Nat := 4983230072969 + 3 ^ 40 * 2602608 * 2
def baseEnd_2602608 : Nat := 98991767350878408735617

theorem tailTrace_2602608 : CollatzResearch.WordTrace tailWord_2602608 prefixEnd_2602608 98991767350878408735617 := by
  unfold tailWord_2602608
  simp only [CollatzResearch.WordTrace]
  refine ⟨47462456077601590451924239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63283274770135453935898985 47462456077601590451924239)
  ·
    refine ⟨71193684116402385677886359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47462456077601590451924239 71193684116402385677886359)
    ·
      refine ⟨106790526174603578516829539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71193684116402385677886359 106790526174603578516829539)
      ·
        refine ⟨160185789261905367775244309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106790526174603578516829539 160185789261905367775244309)
        ·
          refine ⟨7508708871651814114464577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160185789261905367775244309 7508708871651814114464577)
          ·
            refine ⟨5631531653738860585848433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7508708871651814114464577 5631531653738860585848433)
            ·
              refine ⟨4223648740304145439386325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5631531653738860585848433 4223648740304145439386325)
              ·
                refine ⟨98991767350878408735617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4223648740304145439386325 98991767350878408735617)
                ·
                  rfl

theorem cell22_2602608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_2602608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602608 prefixEnd_2602608 := by exact prefixLift 2602608
  have htrace : WordTrace (prefixWord ++ tailWord_2602608) baseStart_2602608 baseEnd_2602608 := by
    simpa [prefixWord, tailWord_2602608, baseEnd_2602608] using wordTrace_append hprefix tailTrace_2602608
  have hstable : (prefixWord ++ tailWord_2602608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602608).length < 2 ^ (prefixWord ++ tailWord_2602608).sum := by decide
  have hdescent : baseEnd_2602608 < baseStart_2602608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602730 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2602730 : Nat := 118140960795 + 2602730 * 2 ^ 59
def prefixEnd_2602730 : Nat := 4983230072969 + 3 ^ 40 * 2602730 * 2
def baseEnd_2602730 : Nat := 890967669251138027070179

theorem tailTrace_2602730 : CollatzResearch.WordTrace tailWord_2602730 prefixEnd_2602730 890967669251138027070179 := by
  unfold tailWord_2602730
  simp only [CollatzResearch.WordTrace]
  refine ⟨23732340465190298934947411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63286241240507463826526429 23732340465190298934947411)
  ·
    refine ⟨35598510697785448402421117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23732340465190298934947411 35598510697785448402421117)
    ·
      refine ⟨13349441511669543150907919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35598510697785448402421117 13349441511669543150907919)
      ·
        refine ⟨20024162267504314726361879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13349441511669543150907919 20024162267504314726361879)
        ·
          refine ⟨30036243401256472089542819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20024162267504314726361879 30036243401256472089542819)
          ·
            refine ⟨45054365101884708134314229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30036243401256472089542819 45054365101884708134314229)
            ·
              refine ⟨4223846728301691387591959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45054365101884708134314229 4223846728301691387591959)
              ·
                refine ⟨6335770092452537081387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223846728301691387591959 6335770092452537081387939)
                ·
                  refine ⟨9503655138678805622081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6335770092452537081387939 9503655138678805622081909)
                  ·
                    refine ⟨890967669251138027070179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9503655138678805622081909 890967669251138027070179)
                    ·
                      rfl

theorem cell22_2602730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2602730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602730 prefixEnd_2602730 := by exact prefixLift 2602730
  have htrace : WordTrace (prefixWord ++ tailWord_2602730) baseStart_2602730 baseEnd_2602730 := by
    simpa [prefixWord, tailWord_2602730, baseEnd_2602730] using wordTrace_append hprefix tailTrace_2602730
  have hstable : (prefixWord ++ tailWord_2602730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602730).length < 2 ^ (prefixWord ++ tailWord_2602730).sum := by decide
  have hdescent : baseEnd_2602730 < baseStart_2602730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602865 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_2602865 : Nat := 118140960795 + 2602865 * 2 ^ 59
def prefixEnd_2602865 : Nat := 4983230072969 + 3 ^ 40 * 2602865 * 2
def baseEnd_2602865 : Nat := 891013882510042674944765

theorem tailTrace_2602865 : CollatzResearch.WordTrace tailWord_2602865 prefixEnd_2602865 891013882510042674944765 := by
  unfold tailWord_2602865
  simp only [CollatzResearch.WordTrace]
  refine ⟨94934285715272113795954049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63289523810181409197302699 94934285715272113795954049)
  ·
    refine ⟨71200714286454085346965537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94934285715272113795954049 71200714286454085346965537)
    ·
      refine ⟨53400535714840564010224153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71200714286454085346965537 53400535714840564010224153)
      ·
        refine ⟨40050401786130423007668115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53400535714840564010224153 40050401786130423007668115)
        ·
          refine ⟨60075602679195634511502173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40050401786130423007668115 60075602679195634511502173)
          ·
            refine ⟨22528351004698362941813315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60075602679195634511502173 22528351004698362941813315)
            ·
              refine ⟨33792526507047544412719973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22528351004698362941813315 33792526507047544412719973)
              ·
                refine ⟨6336098720071414577384995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33792526507047544412719973 6336098720071414577384995)
                ·
                  refine ⟨9504148080107121866077493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6336098720071414577384995 9504148080107121866077493)
                  ·
                    refine ⟨891013882510042674944765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9504148080107121866077493 891013882510042674944765)
                    ·
                      rfl

theorem cell22_2602865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_2602865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602865 prefixEnd_2602865 := by exact prefixLift 2602865
  have htrace : WordTrace (prefixWord ++ tailWord_2602865) baseStart_2602865 baseEnd_2602865 := by
    simpa [prefixWord, tailWord_2602865, baseEnd_2602865] using wordTrace_append hprefix tailTrace_2602865
  have hstable : (prefixWord ++ tailWord_2602865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602865).length < 2 ^ (prefixWord ++ tailWord_2602865).sum := by decide
  have hdescent : baseEnd_2602865 < baseStart_2602865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602880 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_2602880 : Nat := 118140960795 + 2602880 * 2 ^ 59
def prefixEnd_2602880 : Nat := 4983230072969 + 3 ^ 40 * 2602880 * 2
def baseEnd_2602880 : Nat := 891019017316587635819719

theorem tailTrace_2602880 : CollatzResearch.WordTrace tailWord_2602880 prefixEnd_2602880 891019017316587635819719 := by
  unfold tailWord_2602880
  simp only [CollatzResearch.WordTrace]
  refine ⟨47467416405108885678875047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63289888540145180905166729 47467416405108885678875047)
  ·
    refine ⟨71201124607663328518312571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47467416405108885678875047 71201124607663328518312571)
    ·
      refine ⟨106801686911494992777468857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71201124607663328518312571 106801686911494992777468857)
      ·
        refine ⟨80101265183621244583101643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106801686911494992777468857 80101265183621244583101643)
        ·
          refine ⟨120151897775431866874652465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80101265183621244583101643 120151897775431866874652465)
          ·
            refine ⟨90113923331573900155989349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120151897775431866874652465 90113923331573900155989349)
            ·
              refine ⟨16896360624670106279248003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90113923331573900155989349 16896360624670106279248003)
              ·
                refine ⟨25344540937005159418872005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16896360624670106279248003 25344540937005159418872005)
                ·
                  refine ⟨4752101425688467391038501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25344540937005159418872005 4752101425688467391038501)
                  ·
                    refine ⟨891019017316587635819719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752101425688467391038501 891019017316587635819719)
                    ·
                      rfl

theorem cell22_2602880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_2602880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602880 prefixEnd_2602880 := by exact prefixLift 2602880
  have htrace : WordTrace (prefixWord ++ tailWord_2602880) baseStart_2602880 baseEnd_2602880 := by
    simpa [prefixWord, tailWord_2602880, baseEnd_2602880] using wordTrace_append hprefix tailTrace_2602880
  have hstable : (prefixWord ++ tailWord_2602880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602880).length < 2 ^ (prefixWord ++ tailWord_2602880).sum := by decide
  have hdescent : baseEnd_2602880 < baseStart_2602880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602955 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_2602955 : Nat := 118140960795 + 2602955 * 2 ^ 59
def prefixEnd_2602955 : Nat := 4983230072969 + 3 ^ 40 * 2602955 * 2
def baseEnd_2602955 : Nat := 891044691349312440194489

theorem tailTrace_2602955 : CollatzResearch.WordTrace tailWord_2602955 prefixEnd_2602955 891044691349312440194489 := by
  unfold tailWord_2602955
  simp only [CollatzResearch.WordTrace]
  refine ⟨94937568284946059166730319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63291712189964039444486879 94937568284946059166730319)
  ·
    refine ⟨142406352427419088750095479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94937568284946059166730319 142406352427419088750095479)
    ·
      refine ⟨213609528641128633125143219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142406352427419088750095479 213609528641128633125143219)
      ·
        refine ⟨320414292961692949687714829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213609528641128633125143219 320414292961692949687714829)
        ·
          refine ⟨120155359860634856132893061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320414292961692949687714829 120155359860634856132893061)
          ·
            refine ⟨22529129973869035524917449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120155359860634856132893061 22529129973869035524917449)
            ·
              refine ⟨16896847480401776643688087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22529129973869035524917449 16896847480401776643688087)
              ·
                refine ⟨25345271220602664965532131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16896847480401776643688087 25345271220602664965532131)
                ·
                  refine ⟨38017906830903997448298197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25345271220602664965532131 38017906830903997448298197)
                  ·
                    refine ⟨891044691349312440194489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38017906830903997448298197 891044691349312440194489)
                    ·
                      rfl

theorem cell22_2602955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_2602955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602955 prefixEnd_2602955 := by exact prefixLift 2602955
  have htrace : WordTrace (prefixWord ++ tailWord_2602955) baseStart_2602955 baseEnd_2602955 := by
    simpa [prefixWord, tailWord_2602955, baseEnd_2602955] using wordTrace_append hprefix tailTrace_2602955
  have hstable : (prefixWord ++ tailWord_2602955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602955).length < 2 ^ (prefixWord ++ tailWord_2602955).sum := by decide
  have hdescent : baseEnd_2602955 < baseStart_2602955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602987 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 1, 4]
def baseStart_2602987 : Nat := 118140960795 + 2602987 * 2 ^ 59
def prefixEnd_2602987 : Nat := 4983230072969 + 3 ^ 40 * 2602987 * 2
def baseEnd_2602987 : Nat := 891055645603275023394391

theorem tailTrace_2602987 : CollatzResearch.WordTrace tailWord_2602987 prefixEnd_2602987 891055645603275023394391 := by
  unfold tailWord_2602987
  simp only [CollatzResearch.WordTrace]
  refine ⟨94938735420830128631895215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63292490280553419087930143 94938735420830128631895215)
  ·
    refine ⟨142408103131245192947842823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94938735420830128631895215 142408103131245192947842823)
    ·
      refine ⟨213612154696867789421764235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142408103131245192947842823 213612154696867789421764235)
      ·
        refine ⟨320418232045301684132646353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213612154696867789421764235 320418232045301684132646353)
        ·
          refine ⟨240313674033976263099484765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320418232045301684132646353 240313674033976263099484765)
          ·
            refine ⟨90117627762741098662306787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240313674033976263099484765 90117627762741098662306787)
            ·
              refine ⟨135176441644111647993460181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90117627762741098662306787 135176441644111647993460181)
              ·
                refine ⟨3168197851033866749846723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135176441644111647993460181 3168197851033866749846723)
                ·
                  refine ⟨4752296776550800124770085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168197851033866749846723 4752296776550800124770085)
                  ·
                    refine ⟨891055645603275023394391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752296776550800124770085 891055645603275023394391)
                    ·
                      rfl

theorem cell22_2602987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 4].length) (baseStart_2602987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2602987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2602987 prefixEnd_2602987 := by exact prefixLift 2602987
  have htrace : WordTrace (prefixWord ++ tailWord_2602987) baseStart_2602987 baseEnd_2602987 := by
    simpa [prefixWord, tailWord_2602987, baseEnd_2602987] using wordTrace_append hprefix tailTrace_2602987
  have hstable : (prefixWord ++ tailWord_2602987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602987).length < 2 ^ (prefixWord ++ tailWord_2602987).sum := by decide
  have hdescent : baseEnd_2602987 < baseStart_2602987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603017 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_2603017 : Nat := 118140960795 + 2603017 * 2 ^ 59
def prefixEnd_2603017 : Nat := 4983230072969 + 3 ^ 40 * 2603017 * 2
def baseEnd_2603017 : Nat := 891065915216364945144299

theorem tailTrace_2603017 : CollatzResearch.WordTrace tailWord_2603017 prefixEnd_2603017 891065915216364945144299 := by
  unfold tailWord_2603017
  simp only [CollatzResearch.WordTrace]
  refine ⟨94939829610721443755487305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63293219740480962503658203 94939829610721443755487305)
  ·
    refine ⟨71204872208041082816615479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94939829610721443755487305 71204872208041082816615479)
    ·
      refine ⟨106807308312061624224923219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71204872208041082816615479 106807308312061624224923219)
      ·
        refine ⟨160210962468092436337384829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106807308312061624224923219 160210962468092436337384829)
        ·
          refine ⟨60079110925534663626519311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160210962468092436337384829 60079110925534663626519311)
          ·
            refine ⟨90118666388301995439778967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60079110925534663626519311 90118666388301995439778967)
            ·
              refine ⟨135177999582452993159668451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90118666388301995439778967 135177999582452993159668451)
              ·
                refine ⟨202766999373679489739502677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135177999582452993159668451 202766999373679489739502677)
                ·
                  refine ⟨2376175773910306520384797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 202766999373679489739502677 2376175773910306520384797)
                  ·
                    refine ⟨891065915216364945144299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2376175773910306520384797 891065915216364945144299)
                    ·
                      rfl

theorem cell22_2603017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_2603017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603017 prefixEnd_2603017 := by exact prefixLift 2603017
  have htrace : WordTrace (prefixWord ++ tailWord_2603017) baseStart_2603017 baseEnd_2603017 := by
    simpa [prefixWord, tailWord_2603017, baseEnd_2603017] using wordTrace_append hprefix tailTrace_2603017
  have hstable : (prefixWord ++ tailWord_2603017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603017).length < 2 ^ (prefixWord ++ tailWord_2603017).sum := by decide
  have hdescent : baseEnd_2603017 < baseStart_2603017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603032 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_2603032 : Nat := 118140960795 + 2603032 * 2 ^ 59
def prefixEnd_2603032 : Nat := 4983230072969 + 3 ^ 40 * 2603032 * 2
def baseEnd_2603032 : Nat := 891071050022909906019253

theorem tailTrace_2603032 : CollatzResearch.WordTrace tailWord_2603032 prefixEnd_2603032 891071050022909906019253 := by
  unfold tailWord_2603032
  simp only [CollatzResearch.WordTrace]
  refine ⟨47470188352833550658641675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63293584470444734211522233 47470188352833550658641675)
  ·
    refine ⟨71205282529250325987962513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47470188352833550658641675 71205282529250325987962513)
    ·
      refine ⟨53403961896937744490971885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71205282529250325987962513 53403961896937744490971885)
      ·
        refine ⟨20026485711351654184114457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53403961896937744490971885 20026485711351654184114457)
        ·
          refine ⟨15019864283513740638085843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20026485711351654184114457 15019864283513740638085843)
          ·
            refine ⟨22529796425270610957128765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15019864283513740638085843 22529796425270610957128765)
            ·
              refine ⟨8448673659476479108923287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22529796425270610957128765 8448673659476479108923287)
              ·
                refine ⟨12673010489214718663384931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448673659476479108923287 12673010489214718663384931)
                ·
                  refine ⟨19009515733822077995077397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12673010489214718663384931 19009515733822077995077397)
                  ·
                    refine ⟨891071050022909906019253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19009515733822077995077397 891071050022909906019253)
                    ·
                      rfl

theorem cell22_2603032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_2603032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603032 prefixEnd_2603032 := by exact prefixLift 2603032
  have htrace : WordTrace (prefixWord ++ tailWord_2603032) baseStart_2603032 baseEnd_2603032 := by
    simpa [prefixWord, tailWord_2603032, baseEnd_2603032] using wordTrace_append hprefix tailTrace_2603032
  have hstable : (prefixWord ++ tailWord_2603032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603032).length < 2 ^ (prefixWord ++ tailWord_2603032).sum := by decide
  have hdescent : baseEnd_2603032 < baseStart_2603032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603036 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 4]
def baseStart_2603036 : Nat := 118140960795 + 2603036 * 2 ^ 59
def prefixEnd_2603036 : Nat := 4983230072969 + 3 ^ 40 * 2603036 * 2
def baseEnd_2603036 : Nat := 297024139768218409639747

theorem tailTrace_2603036 : CollatzResearch.WordTrace tailWord_2603036 prefixEnd_2603036 297024139768218409639747 := by
  unfold tailWord_2603036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47470261298826305000214481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63293681731768406666952641 47470261298826305000214481)
  ·
    refine ⟨35602695974119728750160861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47470261298826305000214481 35602695974119728750160861)
    ·
      refine ⟨13351010990294898281310323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35602695974119728750160861 13351010990294898281310323)
      ·
        refine ⟨20026516485442347421965485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13351010990294898281310323 20026516485442347421965485)
        ·
          refine ⟨7509943682040880283237057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20026516485442347421965485 7509943682040880283237057)
          ·
            refine ⟨5632457761530660212427793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7509943682040880283237057 5632457761530660212427793)
            ·
              refine ⟨4224343321147995159320845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5632457761530660212427793 4224343321147995159320845)
              ·
                refine ⟨1584128745430498184745317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4224343321147995159320845 1584128745430498184745317)
                ·
                  refine ⟨297024139768218409639747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584128745430498184745317 297024139768218409639747)
                  ·
                    rfl

theorem cell22_2603036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_2603036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603036 prefixEnd_2603036 := by exact prefixLift 2603036
  have htrace : WordTrace (prefixWord ++ tailWord_2603036) baseStart_2603036 baseEnd_2603036 := by
    simpa [prefixWord, tailWord_2603036, baseEnd_2603036] using wordTrace_append hprefix tailTrace_2603036
  have hstable : (prefixWord ++ tailWord_2603036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603036).length < 2 ^ (prefixWord ++ tailWord_2603036).sum := by decide
  have hdescent : baseEnd_2603036 < baseStart_2603036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603079 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 3, 3]
def baseStart_2603079 : Nat := 118140960795 + 2603079 * 2 ^ 59
def prefixEnd_2603079 : Nat := 4983230072969 + 3 ^ 40 * 2603079 * 2
def baseEnd_2603079 : Nat := 891087139083417450094109

theorem tailTrace_2603079 : CollatzResearch.WordTrace tailWord_2603079 prefixEnd_2603079 891087139083417450094109 := by
  unfold tailWord_2603079
  simp only [CollatzResearch.WordTrace]
  refine ⟨94942090936496828344244291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63294727290997885562829527 94942090936496828344244291)
  ·
    refine ⟨142413136404745242516366437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94942090936496828344244291 142413136404745242516366437)
    ·
      refine ⟨26702463075889732971818707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142413136404745242516366437 26702463075889732971818707)
      ·
        refine ⟨40053694613834599457728061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26702463075889732971818707 40053694613834599457728061)
        ·
          refine ⟨15020135480187974796648023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40053694613834599457728061 15020135480187974796648023)
          ·
            refine ⟨22530203220281962194972035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020135480187974796648023 22530203220281962194972035)
            ·
              refine ⟨33795304830422943292458053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22530203220281962194972035 33795304830422943292458053)
              ·
                refine ⟨6336619655704301867335885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33795304830422943292458053 6336619655704301867335885)
                ·
                  refine ⟨2376232370889113200250957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6336619655704301867335885 2376232370889113200250957)
                  ·
                    refine ⟨891087139083417450094109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2376232370889113200250957 891087139083417450094109)
                    ·
                      rfl

theorem cell22_2603079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_2603079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603079 prefixEnd_2603079 := by exact prefixLift 2603079
  have htrace : WordTrace (prefixWord ++ tailWord_2603079) baseStart_2603079 baseEnd_2603079 := by
    simpa [prefixWord, tailWord_2603079, baseEnd_2603079] using wordTrace_append hprefix tailTrace_2603079
  have hstable : (prefixWord ++ tailWord_2603079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603079).length < 2 ^ (prefixWord ++ tailWord_2603079).sum := by decide
  have hdescent : baseEnd_2603079 < baseStart_2603079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603107 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_2603107 : Nat := 118140960795 + 2603107 * 2 ^ 59
def prefixEnd_2603107 : Nat := 4983230072969 + 3 ^ 40 * 2603107 * 2
def baseEnd_2603107 : Nat := 891096724055634710394023

theorem tailTrace_2603107 : CollatzResearch.WordTrace tailWord_2603107 prefixEnd_2603107 891096724055634710394023 := by
  unfold tailWord_2603107
  simp only [CollatzResearch.WordTrace]
  refine ⟨94943112180395389126263575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63295408120263592750842383 94943112180395389126263575)
  ·
    refine ⟨142414668270593083689395363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94943112180395389126263575 142414668270593083689395363)
    ·
      refine ⟨213622002405889625534093045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142414668270593083689395363 213622002405889625534093045)
      ·
        refine ⟨20027062725552152393821223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213622002405889625534093045 20027062725552152393821223)
        ·
          refine ⟨30040594088328228590731835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20027062725552152393821223 30040594088328228590731835)
          ·
            refine ⟨45060891132492342886097753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30040594088328228590731835 45060891132492342886097753)
            ·
              refine ⟨33795668349369257164573315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45060891132492342886097753 33795668349369257164573315)
              ·
                refine ⟨50693502524053885746859973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33795668349369257164573315 50693502524053885746859973)
                ·
                  refine ⟨9505031723260103577536245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50693502524053885746859973 9505031723260103577536245)
                  ·
                    refine ⟨891096724055634710394023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9505031723260103577536245 891096724055634710394023)
                    ·
                      rfl

theorem cell22_2603107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_2603107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603107 prefixEnd_2603107 := by exact prefixLift 2603107
  have htrace : WordTrace (prefixWord ++ tailWord_2603107) baseStart_2603107 baseEnd_2603107 := by
    simpa [prefixWord, tailWord_2603107, baseEnd_2603107] using wordTrace_append hprefix tailTrace_2603107
  have hstable : (prefixWord ++ tailWord_2603107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603107).length < 2 ^ (prefixWord ++ tailWord_2603107).sum := by decide
  have hdescent : baseEnd_2603107 < baseStart_2603107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603113 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 1, 3]
def baseStart_2603113 : Nat := 118140960795 + 2603113 * 2 ^ 59
def prefixEnd_2603113 : Nat := 4983230072969 + 3 ^ 40 * 2603113 * 2
def baseEnd_2603113 : Nat := 891098777978252694744005

theorem tailTrace_2603113 : CollatzResearch.WordTrace tailWord_2603113 prefixEnd_2603113 891098777978252694744005 := by
  unfold tailWord_2603113
  simp only [CollatzResearch.WordTrace]
  refine ⟨94943331018373652150981993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63295554012249101433987995 94943331018373652150981993)
  ·
    refine ⟨71207498263780239113236495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94943331018373652150981993 71207498263780239113236495)
    ·
      refine ⟨106811247395670358669854743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71207498263780239113236495 106811247395670358669854743)
      ·
        refine ⟨160216871093505538004782115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106811247395670358669854743 160216871093505538004782115)
        ·
          refine ⟨240325306640258307007173173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160216871093505538004782115 240325306640258307007173173)
          ·
            refine ⟨22530497497524216281922485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 240325306640258307007173173 22530497497524216281922485)
            ·
              refine ⟨2112234140392895276430233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22530497497524216281922485 2112234140392895276430233)
              ·
                refine ⟨1584175605294671457322675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112234140392895276430233 1584175605294671457322675)
                ·
                  refine ⟨2376263407942007185984013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584175605294671457322675 2376263407942007185984013)
                  ·
                    refine ⟨891098777978252694744005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2376263407942007185984013 891098777978252694744005)
                    ·
                      rfl

theorem cell22_2603113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_2603113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603113 prefixEnd_2603113 := by exact prefixLift 2603113
  have htrace : WordTrace (prefixWord ++ tailWord_2603113) baseStart_2603113 baseEnd_2603113 := by
    simpa [prefixWord, tailWord_2603113, baseEnd_2603113] using wordTrace_append hprefix tailTrace_2603113
  have hstable : (prefixWord ++ tailWord_2603113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603113).length < 2 ^ (prefixWord ++ tailWord_2603113).sum := by decide
  have hdescent : baseEnd_2603113 < baseStart_2603113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603126 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2603126 : Nat := 118140960795 + 2603126 * 2 ^ 59
def prefixEnd_2603126 : Nat := 4983230072969 + 3 ^ 40 * 2603126 * 2
def baseEnd_2603126 : Nat := 297034409381308331389655

theorem tailTrace_2603126 : CollatzResearch.WordTrace tailWord_2603126 prefixEnd_2603126 297034409381308331389655 := by
  unfold tailWord_2603126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933987822957909710700327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63295870111551036914136821 5933987822957909710700327)
  ·
    refine ⟨8900981734436864566050491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5933987822957909710700327 8900981734436864566050491)
    ·
      refine ⟨13351472601655296849075737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8900981734436864566050491 13351472601655296849075737)
      ·
        refine ⟨10013604451241472636806803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13351472601655296849075737 10013604451241472636806803)
        ·
          refine ⟨15020406676862208955210205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10013604451241472636806803 15020406676862208955210205)
          ·
            refine ⟨5632652503823328358203827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15020406676862208955210205 5632652503823328358203827)
            ·
              refine ⟨8448978755734992537305741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632652503823328358203827 8448978755734992537305741)
              ·
                refine ⟨3168367033400622201489653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8448978755734992537305741 3168367033400622201489653)
                ·
                  refine ⟨297034409381308331389655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3168367033400622201489653 297034409381308331389655)
                  ·
                    rfl

theorem cell22_2603126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2603126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603126 prefixEnd_2603126 := by exact prefixLift 2603126
  have htrace : WordTrace (prefixWord ++ tailWord_2603126) baseStart_2603126 baseEnd_2603126 := by
    simpa [prefixWord, tailWord_2603126, baseEnd_2603126] using wordTrace_append hprefix tailTrace_2603126
  have hstable : (prefixWord ++ tailWord_2603126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603126).length < 2 ^ (prefixWord ++ tailWord_2603126).sum := by decide
  have hdescent : baseEnd_2603126 < baseStart_2603126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603139 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 3, 4]
def baseStart_2603139 : Nat := 118140960795 + 2603139 * 2 ^ 59
def prefixEnd_2603139 : Nat := 4983230072969 + 3 ^ 40 * 2603139 * 2
def baseEnd_2603139 : Nat := 891107678309597293593925

theorem tailTrace_2603139 : CollatzResearch.WordTrace tailWord_2603139 prefixEnd_2603139 891107678309597293593925 := by
  unfold tailWord_2603139
  simp only [CollatzResearch.WordTrace]
  refine ⟨94944279316279458591428471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63296186210852972394285647 94944279316279458591428471)
  ·
    refine ⟨142416418974419187887142707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94944279316279458591428471 142416418974419187887142707)
    ·
      refine ⟨213624628461628781830714061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142416418974419187887142707 213624628461628781830714061)
      ·
        refine ⟨80109235673110793186517773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213624628461628781830714061 80109235673110793186517773)
        ·
          refine ⟨30040963377416547444944165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80109235673110793186517773 30040963377416547444944165)
          ·
            refine ⟨5632680633265602645927031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30040963377416547444944165 5632680633265602645927031)
            ·
              refine ⟨8449020949898403968890547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632680633265602645927031 8449020949898403968890547)
              ·
                refine ⟨12673531424847605953335821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449020949898403968890547 12673531424847605953335821)
                ·
                  refine ⟨4752574284317852232500933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12673531424847605953335821 4752574284317852232500933)
                  ·
                    refine ⟨891107678309597293593925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752574284317852232500933 891107678309597293593925)
                    ·
                      rfl

theorem cell22_2603139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_2603139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603139 prefixEnd_2603139 := by exact prefixLift 2603139
  have htrace : WordTrace (prefixWord ++ tailWord_2603139) baseStart_2603139 baseEnd_2603139 := by
    simpa [prefixWord, tailWord_2603139, baseEnd_2603139] using wordTrace_append hprefix tailTrace_2603139
  have hstable : (prefixWord ++ tailWord_2603139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603139).length < 2 ^ (prefixWord ++ tailWord_2603139).sum := by decide
  have hdescent : baseEnd_2603139 < baseStart_2603139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603186 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_2603186 : Nat := 118140960795 + 2603186 * 2 ^ 59
def prefixEnd_2603186 : Nat := 4983230072969 + 3 ^ 40 * 2603186 * 2
def baseEnd_2603186 : Nat := 891123767370104837668781

theorem tailTrace_2603186 : CollatzResearch.WordTrace tailWord_2603186 prefixEnd_2603186 891123767370104837668781 := by
  unfold tailWord_2603186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23736498386777296404597353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63297329031406123745592941 23736498386777296404597353)
  ·
    refine ⟨17802373790082972303448015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23736498386777296404597353 17802373790082972303448015)
    ·
      refine ⟨26703560685124458455172023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17802373790082972303448015 26703560685124458455172023)
      ·
        refine ⟨40055341027686687682758035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26703560685124458455172023 40055341027686687682758035)
        ·
          refine ⟨60083011541530031524137053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40055341027686687682758035 60083011541530031524137053)
          ·
            refine ⟨22531129328073761821551395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60083011541530031524137053 22531129328073761821551395)
            ·
              refine ⟨33796693992110642732327093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22531129328073761821551395 33796693992110642732327093)
              ·
                refine ⟨3168440061760372756155665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33796693992110642732327093 3168440061760372756155665)
                ·
                  refine ⟨2376330046320279567116749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3168440061760372756155665 2376330046320279567116749)
                  ·
                    refine ⟨891123767370104837668781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2376330046320279567116749 891123767370104837668781)
                    ·
                      rfl

theorem cell22_2603186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_2603186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603186 prefixEnd_2603186 := by exact prefixLift 2603186
  have htrace : WordTrace (prefixWord ++ tailWord_2603186) baseStart_2603186 baseEnd_2603186 := by
    simpa [prefixWord, tailWord_2603186, baseEnd_2603186] using wordTrace_append hprefix tailTrace_2603186
  have hstable : (prefixWord ++ tailWord_2603186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603186).length < 2 ^ (prefixWord ++ tailWord_2603186).sum := by decide
  have hdescent : baseEnd_2603186 < baseStart_2603186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603319 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2603319 : Nat := 118140960795 + 2603319 * 2 ^ 59
def prefixEnd_2603319 : Nat := 4983230072969 + 3 ^ 40 * 2603319 * 2
def baseEnd_2603319 : Nat := 891169295988136824093373

theorem tailTrace_2603319 : CollatzResearch.WordTrace tailWord_2603319 prefixEnd_2603319 891169295988136824093373 := by
  unfold tailWord_2603319
  simp only [CollatzResearch.WordTrace]
  refine ⟨94950844455627349332981011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63300562970418232888654007 94950844455627349332981011)
  ·
    refine ⟨142426266683441023999471517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94950844455627349332981011 142426266683441023999471517)
    ·
      refine ⟨53409850006290383999801819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142426266683441023999471517 53409850006290383999801819)
      ·
        refine ⟨80114775009435575999702729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53409850006290383999801819 80114775009435575999702729)
        ·
          refine ⟨60086081257076681999777047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80114775009435575999702729 60086081257076681999777047)
          ·
            refine ⟨90129121885615022999665571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60086081257076681999777047 90129121885615022999665571)
            ·
              refine ⟨135193682828422534499498357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90129121885615022999665571 135193682828422534499498357)
              ·
                refine ⟨12674407765164612609327971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135193682828422534499498357 12674407765164612609327971)
                ·
                  refine ⟨19011611647746918913991957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12674407765164612609327971 19011611647746918913991957)
                  ·
                    refine ⟨891169295988136824093373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19011611647746918913991957 891169295988136824093373)
                    ·
                      rfl

theorem cell22_2603319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2603319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603319 prefixEnd_2603319 := by exact prefixLift 2603319
  have htrace : WordTrace (prefixWord ++ tailWord_2603319) baseStart_2603319 baseEnd_2603319 := by
    simpa [prefixWord, tailWord_2603319, baseEnd_2603319] using wordTrace_append hprefix tailTrace_2603319
  have hstable : (prefixWord ++ tailWord_2603319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603319).length < 2 ^ (prefixWord ++ tailWord_2603319).sum := by decide
  have hdescent : baseEnd_2603319 < baseStart_2603319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603321 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_2603321 : Nat := 118140960795 + 2603321 * 2 ^ 59
def prefixEnd_2603321 : Nat := 4983230072969 + 3 ^ 40 * 2603321 * 2
def baseEnd_2603321 : Nat := 891169980629009485543367

theorem tailTrace_2603321 : CollatzResearch.WordTrace tailWord_2603321 prefixEnd_2603321 891169980629009485543367 := by
  unfold tailWord_2603321
  simp only [CollatzResearch.WordTrace]
  refine ⟨94950917401620103674553817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63300611601080069116369211 94950917401620103674553817)
  ·
    refine ⟨71213188051215077755915363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94950917401620103674553817 71213188051215077755915363)
    ·
      refine ⟨106819782076822616633873045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71213188051215077755915363 106819782076822616633873045)
      ·
        refine ⟨5007177284851060154712799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106819782076822616633873045 5007177284851060154712799)
        ·
          refine ⟨7510765927276590232069199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007177284851060154712799 7510765927276590232069199)
          ·
            refine ⟨11266148890914885348103799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510765927276590232069199 11266148890914885348103799)
            ·
              refine ⟨16899223336372328022155699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266148890914885348103799 16899223336372328022155699)
              ·
                refine ⟨25348835004558492033233549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16899223336372328022155699 25348835004558492033233549)
                ·
                  refine ⟨9505813126709434512462581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25348835004558492033233549 9505813126709434512462581)
                  ·
                    refine ⟨891169980629009485543367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9505813126709434512462581 891169980629009485543367)
                    ·
                      rfl

theorem cell22_2603321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_2603321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603321 prefixEnd_2603321 := by exact prefixLift 2603321
  have htrace : WordTrace (prefixWord ++ tailWord_2603321) baseStart_2603321 baseEnd_2603321 := by
    simpa [prefixWord, tailWord_2603321, baseEnd_2603321] using wordTrace_append hprefix tailTrace_2603321
  have hstable : (prefixWord ++ tailWord_2603321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603321).length < 2 ^ (prefixWord ++ tailWord_2603321).sum := by decide
  have hdescent : baseEnd_2603321 < baseStart_2603321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603336 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_2603336 : Nat := 118140960795 + 2603336 * 2 ^ 59
def prefixEnd_2603336 : Nat := 4983230072969 + 3 ^ 40 * 2603336 * 2
def baseEnd_2603336 : Nat := 891175115435554446418321

theorem tailTrace_2603336 : CollatzResearch.WordTrace tailWord_2603336 prefixEnd_2603336 891175115435554446418321 := by
  unfold tailWord_2603336
  simp only [CollatzResearch.WordTrace]
  refine ⟨47475732248282880618174931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63300976331043840824233241 47475732248282880618174931)
  ·
    refine ⟨71213598372424320927262397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47475732248282880618174931 71213598372424320927262397)
    ·
      refine ⟨26705099389659120347723399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71213598372424320927262397 26705099389659120347723399)
      ·
        refine ⟨40057649084488680521585099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26705099389659120347723399 40057649084488680521585099)
        ·
          refine ⟨60086473626733020782377649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40057649084488680521585099 60086473626733020782377649)
          ·
            refine ⟨45064855220049765586783237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60086473626733020782377649 45064855220049765586783237)
            ·
              refine ⟨8449660353759331047521857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45064855220049765586783237 8449660353759331047521857)
              ·
                refine ⟨6337245265319498285641393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8449660353759331047521857 6337245265319498285641393)
                ·
                  refine ⟨4752933948989623714231045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337245265319498285641393 4752933948989623714231045)
                  ·
                    refine ⟨891175115435554446418321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752933948989623714231045 891175115435554446418321)
                    ·
                      rfl

theorem cell22_2603336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_2603336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603336 prefixEnd_2603336 := by exact prefixLift 2603336
  have htrace : WordTrace (prefixWord ++ tailWord_2603336) baseStart_2603336 baseEnd_2603336 := by
    simpa [prefixWord, tailWord_2603336, baseEnd_2603336] using wordTrace_append hprefix tailTrace_2603336
  have hstable : (prefixWord ++ tailWord_2603336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603336).length < 2 ^ (prefixWord ++ tailWord_2603336).sum := by decide
  have hdescent : baseEnd_2603336 < baseStart_2603336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603368 : List Nat := [2, 1, 4, 2, 2, 2, 3, 6]
def baseStart_2603368 : Nat := 118140960795 + 2603368 * 2 ^ 59
def prefixEnd_2603368 : Nat := 4983230072969 + 3 ^ 40 * 2603368 * 2
def baseEnd_2603368 : Nat := 99020674409946336624247

theorem tailTrace_2603368 : CollatzResearch.WordTrace tailWord_2603368 prefixEnd_2603368 99020674409946336624247 := by
  unfold tailWord_2603368
  simp only [CollatzResearch.WordTrace]
  refine ⟨47476315816224915350757379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63301754421633220467676505 47476315816224915350757379)
  ·
    refine ⟨71214473724337373026136069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47476315816224915350757379 71214473724337373026136069)
    ·
      refine ⟨13352713823313257442400513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71214473724337373026136069 13352713823313257442400513)
      ·
        refine ⟨10014535367484943081800385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13352713823313257442400513 10014535367484943081800385)
        ·
          refine ⟨7510901525613707311350289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10014535367484943081800385 7510901525613707311350289)
          ·
            refine ⟨5633176144210280483512717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7510901525613707311350289 5633176144210280483512717)
            ·
              refine ⟨2112441054078855181317269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5633176144210280483512717 2112441054078855181317269)
              ·
                refine ⟨99020674409946336624247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2112441054078855181317269 99020674409946336624247)
                ·
                  rfl

theorem cell22_2603368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_2603368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603368 prefixEnd_2603368 := by exact prefixLift 2603368
  have htrace : WordTrace (prefixWord ++ tailWord_2603368) baseStart_2603368 baseEnd_2603368 := by
    simpa [prefixWord, tailWord_2603368, baseEnd_2603368] using wordTrace_append hprefix tailTrace_2603368
  have hstable : (prefixWord ++ tailWord_2603368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603368).length < 2 ^ (prefixWord ++ tailWord_2603368).sum := by decide
  have hdescent : baseEnd_2603368 < baseStart_2603368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603370 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2603370 : Nat := 118140960795 + 2603370 * 2 ^ 59
def prefixEnd_2603370 : Nat := 4983230072969 + 3 ^ 40 * 2603370 * 2
def baseEnd_2603370 : Nat := 891186754330389691068217

theorem tailTrace_2603370 : CollatzResearch.WordTrace tailWord_2603370 prefixEnd_2603370 891186754330389691068217 := by
  unfold tailWord_2603370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23738176144610646260771891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63301803052295056695391709 23738176144610646260771891)
  ·
    refine ⟨35607264216915969391157837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23738176144610646260771891 35607264216915969391157837)
    ·
      refine ⟨13352724081343488521684189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35607264216915969391157837 13352724081343488521684189)
      ·
        refine ⟨5007271530503808195631571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13352724081343488521684189 5007271530503808195631571)
        ·
          refine ⟨7510907295755712293447357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007271530503808195631571 7510907295755712293447357)
          ·
            refine ⟨2816590235908392110042759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7510907295755712293447357 2816590235908392110042759)
            ·
              refine ⟨4224885353862588165064139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816590235908392110042759 4224885353862588165064139)
              ·
                refine ⟨6337328030793882247596209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224885353862588165064139 6337328030793882247596209)
                ·
                  refine ⟨4752996023095411685697157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337328030793882247596209 4752996023095411685697157)
                  ·
                    refine ⟨891186754330389691068217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752996023095411685697157 891186754330389691068217)
                    ·
                      rfl

theorem cell22_2603370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2603370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603370 prefixEnd_2603370 := by exact prefixLift 2603370
  have htrace : WordTrace (prefixWord ++ tailWord_2603370) baseStart_2603370 baseEnd_2603370 := by
    simpa [prefixWord, tailWord_2603370, baseEnd_2603370] using wordTrace_append hprefix tailTrace_2603370
  have hstable : (prefixWord ++ tailWord_2603370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603370).length < 2 ^ (prefixWord ++ tailWord_2603370).sum := by decide
  have hdescent : baseEnd_2603370 < baseStart_2603370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603379 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 9]
def baseStart_2603379 : Nat := 118140960795 + 2603379 * 2 ^ 59
def prefixEnd_2603379 : Nat := 4983230072969 + 3 ^ 40 * 2603379 * 2
def baseEnd_2603379 : Nat := 297063278404772222531063

theorem tailTrace_2603379 : CollatzResearch.WordTrace tailWord_2603379 prefixEnd_2603379 297063278404772222531063 := by
  unfold tailWord_2603379
  simp only [CollatzResearch.WordTrace]
  refine ⟨94953032835409979580165191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63302021890273319720110127 94953032835409979580165191)
  ·
    refine ⟨142429549253114969370247787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94953032835409979580165191 142429549253114969370247787)
    ·
      refine ⟨213644323879672454055371681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142429549253114969370247787 213644323879672454055371681)
      ·
        refine ⟨160233242909754340541528761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213644323879672454055371681 160233242909754340541528761)
        ·
          refine ⟨120174932182315755406146571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160233242909754340541528761 120174932182315755406146571)
          ·
            refine ⟨180262398273473633109219857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120174932182315755406146571 180262398273473633109219857)
            ·
              refine ⟨135196798705105224831914893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180262398273473633109219857 135196798705105224831914893)
              ·
                refine ⟨50698799514414459311968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135196798705105224831914893 50698799514414459311968085)
                ·
                  refine ⟨297063278404772222531063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50698799514414459311968085 297063278404772222531063)
                  ·
                    rfl

theorem cell22_2603379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_2603379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603379 prefixEnd_2603379 := by exact prefixLift 2603379
  have htrace : WordTrace (prefixWord ++ tailWord_2603379) baseStart_2603379 baseEnd_2603379 := by
    simpa [prefixWord, tailWord_2603379, baseEnd_2603379] using wordTrace_append hprefix tailTrace_2603379
  have hstable : (prefixWord ++ tailWord_2603379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603379).length < 2 ^ (prefixWord ++ tailWord_2603379).sum := by decide
  have hdescent : baseEnd_2603379 < baseStart_2603379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603396 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_2603396 : Nat := 118140960795 + 2603396 * 2 ^ 59
def prefixEnd_2603396 : Nat := 4983230072969 + 3 ^ 40 * 2603396 * 2
def baseEnd_2603396 : Nat := 297065218220578096639379

theorem tailTrace_2603396 : CollatzResearch.WordTrace tailWord_2603396 prefixEnd_2603396 297065218220578096639379 := by
  unfold tailWord_2603396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47476826438174195741767021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63302435250898927655689361 47476826438174195741767021)
  ·
    refine ⟨17803809914315323403162633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47476826438174195741767021 17803809914315323403162633)
    ·
      refine ⟨13352857435736492552371975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17803809914315323403162633 13352857435736492552371975)
      ·
        refine ⟨20029286153604738828557963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13352857435736492552371975 20029286153604738828557963)
        ·
          refine ⟨30043929230407108242836945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20029286153604738828557963 30043929230407108242836945)
          ·
            refine ⟨22532946922805331182127709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30043929230407108242836945 22532946922805331182127709)
            ·
              refine ⟨8449855096051999193297891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22532946922805331182127709 8449855096051999193297891)
              ·
                refine ⟨12674782644077998789946837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449855096051999193297891 12674782644077998789946837)
                ·
                  refine ⟨297065218220578096639379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12674782644077998789946837 297065218220578096639379)
                  ·
                    rfl

theorem cell22_2603396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_2603396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603396 prefixEnd_2603396 := by exact prefixLift 2603396
  have htrace : WordTrace (prefixWord ++ tailWord_2603396) baseStart_2603396 baseEnd_2603396 := by
    simpa [prefixWord, tailWord_2603396, baseEnd_2603396] using wordTrace_append hprefix tailTrace_2603396
  have hstable : (prefixWord ++ tailWord_2603396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603396).length < 2 ^ (prefixWord ++ tailWord_2603396).sum := by decide
  have hdescent : baseEnd_2603396 < baseStart_2603396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603400 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 1, 3]
def baseStart_2603400 : Nat := 118140960795 + 2603400 * 2 ^ 59
def prefixEnd_2603400 : Nat := 4983230072969 + 3 ^ 40 * 2603400 * 2
def baseEnd_2603400 : Nat := 891197023943479612818125

theorem tailTrace_2603400 : CollatzResearch.WordTrace tailWord_2603400 prefixEnd_2603400 891197023943479612818125 := by
  unfold tailWord_2603400
  simp only [CollatzResearch.WordTrace]
  refine ⟨47476899384166950083339827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63302532512222600111119769 47476899384166950083339827)
  ·
    refine ⟨71215349076250425125009741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47476899384166950083339827 71215349076250425125009741)
    ·
      refine ⟨26705755903593909421878653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71215349076250425125009741 26705755903593909421878653)
      ·
        refine ⟨10014658463847716033204495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26705755903593909421878653 10014658463847716033204495)
        ·
          refine ⟨15021987695771574049806743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10014658463847716033204495 15021987695771574049806743)
          ·
            refine ⟨22532981543657361074710115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15021987695771574049806743 22532981543657361074710115)
            ·
              refine ⟨33799472315486041612065173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22532981543657361074710115 33799472315486041612065173)
              ·
                refine ⟨1584350264788408200565555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33799472315486041612065173 1584350264788408200565555)
                ·
                  refine ⟨2376525397182612300848333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584350264788408200565555 2376525397182612300848333)
                  ·
                    refine ⟨891197023943479612818125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2376525397182612300848333 891197023943479612818125)
                    ·
                      rfl

theorem cell22_2603400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_2603400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603400 prefixEnd_2603400 := by exact prefixLift 2603400
  have htrace : WordTrace (prefixWord ++ tailWord_2603400) baseStart_2603400 baseEnd_2603400 := by
    simpa [prefixWord, tailWord_2603400, baseEnd_2603400] using wordTrace_append hprefix tailTrace_2603400
  have hstable : (prefixWord ++ tailWord_2603400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603400).length < 2 ^ (prefixWord ++ tailWord_2603400).sum := by decide
  have hdescent : baseEnd_2603400 < baseStart_2603400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603471 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 6, 4]
def baseStart_2603471 : Nat := 118140960795 + 2603471 * 2 ^ 59
def prefixEnd_2603471 : Nat := 4983230072969 + 3 ^ 40 * 2603471 * 2
def baseEnd_2603471 : Nat := 891221328694459094292907

theorem tailTrace_2603471 : CollatzResearch.WordTrace tailWord_2603471 prefixEnd_2603471 891221328694459094292907 := by
  unfold tailWord_2603471
  simp only [CollatzResearch.WordTrace]
  refine ⟨94956388351076679292514267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63304258900717786195009511 94956388351076679292514267)
  ·
    refine ⟨142434582526615018938771401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94956388351076679292514267 142434582526615018938771401)
    ·
      refine ⟨106825936894961264204078551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142434582526615018938771401 106825936894961264204078551)
      ·
        refine ⟨160238905342441896306117827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106825936894961264204078551 160238905342441896306117827)
        ·
          refine ⟨240358358013662844459176741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160238905342441896306117827 240358358013662844459176741)
          ·
            refine ⟨45067192127561783336095639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240358358013662844459176741 45067192127561783336095639)
            ·
              refine ⟨67600788191342675004143459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45067192127561783336095639 67600788191342675004143459)
              ·
                refine ⟨101401182287014012506215189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67600788191342675004143459 101401182287014012506215189)
                ·
                  refine ⟨4753180419703781836228837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101401182287014012506215189 4753180419703781836228837)
                  ·
                    refine ⟨891221328694459094292907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753180419703781836228837 891221328694459094292907)
                    ·
                      rfl

theorem cell22_2603471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_2603471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603471 prefixEnd_2603471 := by exact prefixLift 2603471
  have htrace : WordTrace (prefixWord ++ tailWord_2603471) baseStart_2603471 baseEnd_2603471 := by
    simpa [prefixWord, tailWord_2603471, baseEnd_2603471] using wordTrace_append hprefix tailTrace_2603471
  have hstable : (prefixWord ++ tailWord_2603471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603471).length < 2 ^ (prefixWord ++ tailWord_2603471).sum := by decide
  have hdescent : baseEnd_2603471 < baseStart_2603471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603488 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_2603488 : Nat := 118140960795 + 2603488 * 2 ^ 59
def prefixEnd_2603488 : Nat := 4983230072969 + 3 ^ 40 * 2603488 * 2
def baseEnd_2603488 : Nat := 891227148141876716617855

theorem tailTrace_2603488 : CollatzResearch.WordTrace tailWord_2603488 prefixEnd_2603488 891227148141876716617855 := by
  unfold tailWord_2603488
  simp only [CollatzResearch.WordTrace]
  refine ⟨47478504196007545597941559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63304672261343394130588745 47478504196007545597941559)
  ·
    refine ⟨71217756294011318396912339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47478504196007545597941559 71217756294011318396912339)
    ·
      refine ⟨106826634441016977595368509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71217756294011318396912339 106826634441016977595368509)
      ·
        refine ⟨40059987915381366598263191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106826634441016977595368509 40059987915381366598263191)
        ·
          refine ⟨60089981873072049897394787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40059987915381366598263191 60089981873072049897394787)
          ·
            refine ⟨90134972809608074846092181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60089981873072049897394787 90134972809608074846092181)
            ·
              refine ⟨4225076850450378508410571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90134972809608074846092181 4225076850450378508410571)
              ·
                refine ⟨6337615275675567762615857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225076850450378508410571 6337615275675567762615857)
                ·
                  refine ⟨4753211456756675821961893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337615275675567762615857 4753211456756675821961893)
                  ·
                    refine ⟨891227148141876716617855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753211456756675821961893 891227148141876716617855)
                    ·
                      rfl

theorem cell22_2603488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_2603488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603488 prefixEnd_2603488 := by exact prefixLift 2603488
  have htrace : WordTrace (prefixWord ++ tailWord_2603488) baseStart_2603488 baseEnd_2603488 := by
    simpa [prefixWord, tailWord_2603488, baseEnd_2603488] using wordTrace_append hprefix tailTrace_2603488
  have hstable : (prefixWord ++ tailWord_2603488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603488).length < 2 ^ (prefixWord ++ tailWord_2603488).sum := by decide
  have hdescent : baseEnd_2603488 < baseStart_2603488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603608 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_2603608 : Nat := 118140960795 + 2603608 * 2 ^ 59
def prefixEnd_2603608 : Nat := 4983230072969 + 3 ^ 40 * 2603608 * 2
def baseEnd_2603608 : Nat := 891268226594236403617487

theorem tailTrace_2603608 : CollatzResearch.WordTrace tailWord_2603608 prefixEnd_2603608 891268226594236403617487 := by
  unfold tailWord_2603608
  simp only [CollatzResearch.WordTrace]
  refine ⟨47480692575790175845125739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63307590101053567793500985 47480692575790175845125739)
  ·
    refine ⟨71221038863685263767688609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47480692575790175845125739 71221038863685263767688609)
    ·
      refine ⟨53415779147763947825766457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71221038863685263767688609 53415779147763947825766457)
      ·
        refine ⟨40061834360822960869324843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53415779147763947825766457 40061834360822960869324843)
        ·
          refine ⟨60092751541234441303987265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40061834360822960869324843 60092751541234441303987265)
          ·
            refine ⟨45069563655925830977990449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60092751541234441303987265 45069563655925830977990449)
            ·
              refine ⟨33802172741944373233492837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45069563655925830977990449 33802172741944373233492837)
              ·
                refine ⟨6337907389114569981279907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33802172741944373233492837 6337907389114569981279907)
                ·
                  refine ⟨9506861083671854971919861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6337907389114569981279907 9506861083671854971919861)
                  ·
                    refine ⟨891268226594236403617487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9506861083671854971919861 891268226594236403617487)
                    ·
                      rfl

theorem cell22_2603608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_2603608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603608 prefixEnd_2603608 := by exact prefixLift 2603608
  have htrace : WordTrace (prefixWord ++ tailWord_2603608) baseStart_2603608 baseEnd_2603608 := by
    simpa [prefixWord, tailWord_2603608, baseEnd_2603608] using wordTrace_append hprefix tailTrace_2603608
  have hstable : (prefixWord ++ tailWord_2603608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603608).length < 2 ^ (prefixWord ++ tailWord_2603608).sum := by decide
  have hdescent : baseEnd_2603608 < baseStart_2603608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603625 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_2603625 : Nat := 118140960795 + 2603625 * 2 ^ 59
def prefixEnd_2603625 : Nat := 4983230072969 + 3 ^ 40 * 2603625 * 2
def baseEnd_2603625 : Nat := 891274046041654025942435

theorem tailTrace_2603625 : CollatzResearch.WordTrace tailWord_2603625 prefixEnd_2603625 891274046041654025942435 := by
  unfold tailWord_2603625
  simp only [CollatzResearch.WordTrace]
  refine ⟨94962005192518763593620329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63308003461679175729080219 94962005192518763593620329)
  ·
    refine ⟨71221503894389072695215247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94962005192518763593620329 71221503894389072695215247)
    ·
      refine ⟨106832255841583609042822871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71221503894389072695215247 106832255841583609042822871)
      ·
        refine ⟨160248383762375413564234307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106832255841583609042822871 160248383762375413564234307)
        ·
          refine ⟨240372575643563120346351461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160248383762375413564234307 240372575643563120346351461)
          ·
            refine ⟨45069857933168085064940899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240372575643563120346351461 45069857933168085064940899)
            ·
              refine ⟨67604786899752127597411349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45069857933168085064940899 67604786899752127597411349)
              ·
                refine ⟨3168974385925880981128657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67604786899752127597411349 3168974385925880981128657)
                ·
                  refine ⟨2376730789444410735846493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3168974385925880981128657 2376730789444410735846493)
                  ·
                    refine ⟨891274046041654025942435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2376730789444410735846493 891274046041654025942435)
                    ·
                      rfl

theorem cell22_2603625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_2603625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603625 prefixEnd_2603625 := by exact prefixLift 2603625
  have htrace : WordTrace (prefixWord ++ tailWord_2603625) baseStart_2603625 baseEnd_2603625 := by
    simpa [prefixWord, tailWord_2603625, baseEnd_2603625] using wordTrace_append hprefix tailTrace_2603625
  have hstable : (prefixWord ++ tailWord_2603625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603625).length < 2 ^ (prefixWord ++ tailWord_2603625).sum := by decide
  have hdescent : baseEnd_2603625 < baseStart_2603625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603745 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 6]
def baseStart_2603745 : Nat := 118140960795 + 2603745 * 2 ^ 59
def prefixEnd_2603745 : Nat := 4983230072969 + 3 ^ 40 * 2603745 * 2
def baseEnd_2603745 : Nat := 297105041498004570980689

theorem tailTrace_2603745 : CollatzResearch.WordTrace tailWord_2603745 prefixEnd_2603745 297105041498004570980689 := by
  unfold tailWord_2603745
  simp only [CollatzResearch.WordTrace]
  refine ⟨94966381952084024087988689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63310921301389349391992459 94966381952084024087988689)
  ·
    refine ⟨71224786464063018065991517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94966381952084024087988689 71224786464063018065991517)
    ·
      refine ⟨26709294924023631774746819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71224786464063018065991517 26709294924023631774746819)
      ·
        refine ⟨40063942386035447662120229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26709294924023631774746819 40063942386035447662120229)
        ·
          refine ⟨7511989197381646436647543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40063942386035447662120229 7511989197381646436647543)
          ·
            refine ⟨11267983796072469654971315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511989197381646436647543 11267983796072469654971315)
            ·
              refine ⟨16901975694108704482456973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11267983796072469654971315 16901975694108704482456973)
              ·
                refine ⟨6338240885290764180921365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16901975694108704482456973 6338240885290764180921365)
                ·
                  refine ⟨297105041498004570980689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6338240885290764180921365 297105041498004570980689)
                  ·
                    rfl

theorem cell22_2603745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_2603745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603745 prefixEnd_2603745 := by exact prefixLift 2603745
  have htrace : WordTrace (prefixWord ++ tailWord_2603745) baseStart_2603745 baseEnd_2603745 := by
    simpa [prefixWord, tailWord_2603745, baseEnd_2603745] using wordTrace_append hprefix tailTrace_2603745
  have hstable : (prefixWord ++ tailWord_2603745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603745).length < 2 ^ (prefixWord ++ tailWord_2603745).sum := by decide
  have hdescent : baseEnd_2603745 < baseStart_2603745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603775 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 2, 4]
def baseStart_2603775 : Nat := 118140960795 + 2603775 * 2 ^ 59
def prefixEnd_2603775 : Nat := 4983230072969 + 3 ^ 40 * 2603775 * 2
def baseEnd_2603775 : Nat := 891325394107103634691975

theorem tailTrace_2603775 : CollatzResearch.WordTrace tailWord_2603775 prefixEnd_2603775 891325394107103634691975 := by
  unfold tailWord_2603775
  simp only [CollatzResearch.WordTrace]
  refine ⟨94967476141975339211580779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63311650761316892807720519 94967476141975339211580779)
  ·
    refine ⟨142451214212963008817371169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94967476141975339211580779 142451214212963008817371169)
    ·
      refine ⟨106838410659722256613028377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142451214212963008817371169 106838410659722256613028377)
      ·
        refine ⟨80128807994791692459771283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106838410659722256613028377 80128807994791692459771283)
        ·
          refine ⟨120193211992187538689656925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80128807994791692459771283 120193211992187538689656925)
          ·
            refine ⟨45072454497070327008621347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120193211992187538689656925 45072454497070327008621347)
            ·
              refine ⟨67608681745605490512932021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45072454497070327008621347 67608681745605490512932021)
              ·
                refine ⟨6338313913650514735587377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67608681745605490512932021 6338313913650514735587377)
                ·
                  refine ⟨4753735435237886051690533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6338313913650514735587377 4753735435237886051690533)
                  ·
                    refine ⟨891325394107103634691975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753735435237886051690533 891325394107103634691975)
                    ·
                      rfl

theorem cell22_2603775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_2603775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603775 prefixEnd_2603775 := by exact prefixLift 2603775
  have htrace : WordTrace (prefixWord ++ tailWord_2603775) baseStart_2603775 baseEnd_2603775 := by
    simpa [prefixWord, tailWord_2603775, baseEnd_2603775] using wordTrace_append hprefix tailTrace_2603775
  have hstable : (prefixWord ++ tailWord_2603775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603775).length < 2 ^ (prefixWord ++ tailWord_2603775).sum := by decide
  have hdescent : baseEnd_2603775 < baseStart_2603775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603852 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_2603852 : Nat := 118140960795 + 2603852 * 2 ^ 59
def prefixEnd_2603852 : Nat := 4983230072969 + 3 ^ 40 * 2603852 * 2
def baseEnd_2603852 : Nat := 297117250926900366838913

theorem tailTrace_2603852 : CollatzResearch.WordTrace tailWord_2603852 prefixEnd_2603852 297117250926900366838913 := by
  unfold tailWord_2603852
  simp only [CollatzResearch.WordTrace]
  refine ⟨47485142281348190681066905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63313523041797587574755873 47485142281348190681066905)
  ·
    refine ⟨35613856711011143010800179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47485142281348190681066905 35613856711011143010800179)
    ·
      refine ⟨53420785066516714516200269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35613856711011143010800179 53420785066516714516200269)
      ·
        refine ⟨20032794399943767943575101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53420785066516714516200269 20032794399943767943575101)
        ·
          refine ⟨7512297899978912978840663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20032794399943767943575101 7512297899978912978840663)
          ·
            refine ⟨11268446849968369468260995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7512297899978912978840663 11268446849968369468260995)
            ·
              refine ⟨16902670274952554202391493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11268446849968369468260995 16902670274952554202391493)
              ·
                refine ⟨3169250676553603912948405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16902670274952554202391493 3169250676553603912948405)
                ·
                  refine ⟨297117250926900366838913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3169250676553603912948405 297117250926900366838913)
                  ·
                    rfl

theorem cell22_2603852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_2603852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603852 prefixEnd_2603852 := by exact prefixLift 2603852
  have htrace : WordTrace (prefixWord ++ tailWord_2603852) baseStart_2603852 baseEnd_2603852 := by
    simpa [prefixWord, tailWord_2603852, baseEnd_2603852] using wordTrace_append hprefix tailTrace_2603852
  have hstable : (prefixWord ++ tailWord_2603852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603852).length < 2 ^ (prefixWord ++ tailWord_2603852).sum := by decide
  have hdescent : baseEnd_2603852 < baseStart_2603852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603856 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 1, 3]
def baseStart_2603856 : Nat := 118140960795 + 2603856 * 2 ^ 59
def prefixEnd_2603856 : Nat := 4983230072969 + 3 ^ 40 * 2603856 * 2
def baseEnd_2603856 : Nat := 891353122062446423416727

theorem tailTrace_2603856 : CollatzResearch.WordTrace tailWord_2603856 prefixEnd_2603856 891353122062446423416727 := by
  unfold tailWord_2603856
  simp only [CollatzResearch.WordTrace]
  refine ⟨47485215227340945022639711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63313620303121260030186281 47485215227340945022639711)
  ·
    refine ⟨71227822841011417533959567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47485215227340945022639711 71227822841011417533959567)
    ·
      refine ⟨106841734261517126300939351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71227822841011417533959567 106841734261517126300939351)
      ·
        refine ⟨160262601392275689451409027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106841734261517126300939351 160262601392275689451409027)
        ·
          refine ⟨240393902088413534177113541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160262601392275689451409027 240393902088413534177113541)
          ·
            refine ⟨45073856641577537658208789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240393902088413534177113541 45073856641577537658208789)
            ·
              refine ⟨2112837030073947077728537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45073856641577537658208789 2112837030073947077728537)
              ·
                refine ⟨1584627772555460308296403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112837030073947077728537 1584627772555460308296403)
                ·
                  refine ⟨2376941658833190462444605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584627772555460308296403 2376941658833190462444605)
                  ·
                    refine ⟨891353122062446423416727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2376941658833190462444605 891353122062446423416727)
                    ·
                      rfl

theorem cell22_2603856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_2603856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603856 prefixEnd_2603856 := by exact prefixLift 2603856
  have htrace : WordTrace (prefixWord ++ tailWord_2603856) baseStart_2603856 baseEnd_2603856 := by
    simpa [prefixWord, tailWord_2603856, baseEnd_2603856] using wordTrace_append hprefix tailTrace_2603856
  have hstable : (prefixWord ++ tailWord_2603856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603856).length < 2 ^ (prefixWord ++ tailWord_2603856).sum := by decide
  have hdescent : baseEnd_2603856 < baseStart_2603856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603899 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 1, 4]
def baseStart_2603899 : Nat := 118140960795 + 2603899 * 2 ^ 59
def prefixEnd_2603899 : Nat := 4983230072969 + 3 ^ 40 * 2603899 * 2
def baseEnd_2603899 : Nat := 891367841841208644591595

theorem tailTrace_2603899 : CollatzResearch.WordTrace tailWord_2603899 prefixEnd_2603899 891367841841208644591595 := by
  unfold tailWord_2603899
  simp only [CollatzResearch.WordTrace]
  refine ⟨94971998793526108389094751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63314665862350738926063167 94971998793526108389094751)
  ·
    refine ⟨142457998190289162583642127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94971998793526108389094751 142457998190289162583642127)
    ·
      refine ⟨213686997285433743875463191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142457998190289162583642127 213686997285433743875463191)
      ·
        refine ⟨320530495928150615813194787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213686997285433743875463191 320530495928150615813194787)
        ·
          refine ⟨480795743892225923719792181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320530495928150615813194787 480795743892225923719792181)
          ·
            refine ⟨45074600989896180348730517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 480795743892225923719792181 45074600989896180348730517)
            ·
              refine ⟨2112871921401383453846743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45074600989896180348730517 2112871921401383453846743)
              ·
                refine ⟨3169307882102075180770115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112871921401383453846743 3169307882102075180770115)
                ·
                  refine ⟨4753961823153112771155173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169307882102075180770115 4753961823153112771155173)
                  ·
                    refine ⟨891367841841208644591595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753961823153112771155173 891367841841208644591595)
                    ·
                      rfl

theorem cell22_2603899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 4].length) (baseStart_2603899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603899 prefixEnd_2603899 := by exact prefixLift 2603899
  have htrace : WordTrace (prefixWord ++ tailWord_2603899) baseStart_2603899 baseEnd_2603899 := by
    simpa [prefixWord, tailWord_2603899, baseEnd_2603899] using wordTrace_append hprefix tailTrace_2603899
  have hstable : (prefixWord ++ tailWord_2603899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603899).length < 2 ^ (prefixWord ++ tailWord_2603899).sum := by decide
  have hdescent : baseEnd_2603899 < baseStart_2603899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603914 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_2603914 : Nat := 118140960795 + 2603914 * 2 ^ 59
def prefixEnd_2603914 : Nat := 4983230072969 + 3 ^ 40 * 2603914 * 2
def baseEnd_2603914 : Nat := 297124325549251201822183

theorem tailTrace_2603914 : CollatzResearch.WordTrace tailWord_2603914 prefixEnd_2603914 297124325549251201822183 := by
  unfold tailWord_2603914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743136472117941487722699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63315030592314510633927197 23743136472117941487722699)
  ·
    refine ⟨35614704708176912231584049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743136472117941487722699 35614704708176912231584049)
    ·
      refine ⟨26711028531132684173688037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35614704708176912231584049 26711028531132684173688037)
      ·
        refine ⟨5008317849587378282566507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26711028531132684173688037 5008317849587378282566507)
        ·
          refine ⟨7512476774381067423849761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008317849587378282566507 7512476774381067423849761)
          ·
            refine ⟨5634357580785800567887321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512476774381067423849761 5634357580785800567887321)
            ·
              refine ⟨4225768185589350425915491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634357580785800567887321 4225768185589350425915491)
              ·
                refine ⟨6338652278384025638873237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225768185589350425915491 6338652278384025638873237)
                ·
                  refine ⟨297124325549251201822183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6338652278384025638873237 297124325549251201822183)
                  ·
                    rfl

theorem cell22_2603914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_2603914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2603914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2603914 prefixEnd_2603914 := by exact prefixLift 2603914
  have htrace : WordTrace (prefixWord ++ tailWord_2603914) baseStart_2603914 baseEnd_2603914 := by
    simpa [prefixWord, tailWord_2603914, baseEnd_2603914] using wordTrace_append hprefix tailTrace_2603914
  have hstable : (prefixWord ++ tailWord_2603914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603914).length < 2 ^ (prefixWord ++ tailWord_2603914).sum := by decide
  have hdescent : baseEnd_2603914 < baseStart_2603914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604066 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2604066 : Nat := 118140960795 + 2604066 * 2 ^ 59
def prefixEnd_2604066 : Nat := 4983230072969 + 3 ^ 40 * 2604066 * 2
def baseEnd_2604066 : Nat := 297141669784691958555361

theorem tailTrace_2604066 : CollatzResearch.WordTrace tailWord_2604066 prefixEnd_2604066 297141669784691958555361 := by
  unfold tailWord_2604066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23744522445980273977606013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63318726522614063940282701 23744522445980273977606013)
  ·
    refine ⟨8904195917242602741602255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23744522445980273977606013 8904195917242602741602255)
    ·
      refine ⟨13356293875863904112403383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904195917242602741602255 13356293875863904112403383)
      ·
        refine ⟨20034440813795856168605075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13356293875863904112403383 20034440813795856168605075)
        ·
          refine ⟨30051661220693784252907613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20034440813795856168605075 30051661220693784252907613)
          ·
            refine ⟨11269372957760169094840355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30051661220693784252907613 11269372957760169094840355)
            ·
              refine ⟨16904059436640253642260533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11269372957760169094840355 16904059436640253642260533)
              ·
                refine ⟨1584755572185023778961925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16904059436640253642260533 1584755572185023778961925)
                ·
                  refine ⟨297141669784691958555361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584755572185023778961925 297141669784691958555361)
                  ·
                    rfl

theorem cell22_2604066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2604066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604066 prefixEnd_2604066 := by exact prefixLift 2604066
  have htrace : WordTrace (prefixWord ++ tailWord_2604066) baseStart_2604066 baseEnd_2604066 := by
    simpa [prefixWord, tailWord_2604066, baseEnd_2604066] using wordTrace_append hprefix tailTrace_2604066
  have hstable : (prefixWord ++ tailWord_2604066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604066).length < 2 ^ (prefixWord ++ tailWord_2604066).sum := by decide
  have hdescent : baseEnd_2604066 < baseStart_2604066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604068 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_2604068 : Nat := 118140960795 + 2604068 * 2 ^ 59
def prefixEnd_2604068 : Nat := 4983230072969 + 3 ^ 40 * 2604068 * 2
def baseEnd_2604068 : Nat := 891425693994948537116077

theorem tailTrace_2604068 : CollatzResearch.WordTrace tailWord_2604068 prefixEnd_2604068 891425693994948537116077 := by
  unfold tailWord_2604068
  simp only [CollatzResearch.WordTrace]
  refine ⟨47489081364956925125998429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63318775153275900167997905 47489081364956925125998429)
  ·
    refine ⟨17808405511858846922249411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47489081364956925125998429 17808405511858846922249411)
    ·
      refine ⟨26712608267788270383374117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17808405511858846922249411 26712608267788270383374117)
      ·
        refine ⟨5008614050210300696882647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26712608267788270383374117 5008614050210300696882647)
        ·
          refine ⟨7512921075315451045323971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008614050210300696882647 7512921075315451045323971)
          ·
            refine ⟨11269381612973176567985957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7512921075315451045323971 11269381612973176567985957)
            ·
              refine ⟨2113009052432470606497367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11269381612973176567985957 2113009052432470606497367)
              ·
                refine ⟨3169513578648705909746051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113009052432470606497367 3169513578648705909746051)
                ·
                  refine ⟨4754270367973058864619077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169513578648705909746051 4754270367973058864619077)
                  ·
                    refine ⟨891425693994948537116077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754270367973058864619077 891425693994948537116077)
                    ·
                      rfl

theorem cell22_2604068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_2604068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604068 prefixEnd_2604068 := by exact prefixLift 2604068
  have htrace : WordTrace (prefixWord ++ tailWord_2604068) baseStart_2604068 baseEnd_2604068 := by
    simpa [prefixWord, tailWord_2604068, baseEnd_2604068] using wordTrace_append hprefix tailTrace_2604068
  have hstable : (prefixWord ++ tailWord_2604068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604068).length < 2 ^ (prefixWord ++ tailWord_2604068).sum := by decide
  have hdescent : baseEnd_2604068 < baseStart_2604068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604149 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2604149 : Nat := 118140960795 + 2604149 * 2 ^ 59
def prefixEnd_2604149 : Nat := 4983230072969 + 3 ^ 40 * 2604149 * 2
def baseEnd_2604149 : Nat := 891453421950291325840829

theorem tailTrace_2604149 : CollatzResearch.WordTrace tailWord_2604149 prefixEnd_2604149 891453421950291325840829 := by
  unfold tailWord_2604149
  simp only [CollatzResearch.WordTrace]
  refine ⟨94981117042620401085695501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63320744695080267390463667 94981117042620401085695501)
  ·
    refine ⟨35617918890982650407135813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94981117042620401085695501 35617918890982650407135813)
    ·
      refine ⟨6678359792059246951337965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35617918890982650407135813 6678359792059246951337965)
      ·
        refine ⟨2504384922022217606751737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6678359792059246951337965 2504384922022217606751737)
        ·
          refine ⟨1878288691516663205063803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504384922022217606751737 1878288691516663205063803)
          ·
            refine ⟨2817433037274994807595705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878288691516663205063803 2817433037274994807595705)
            ·
              refine ⟨2113074777956246105696779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2817433037274994807595705 2113074777956246105696779)
              ·
                refine ⟨3169612166934369158545169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113074777956246105696779 3169612166934369158545169)
                ·
                  refine ⟨2377209125200776868908877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169612166934369158545169 2377209125200776868908877)
                  ·
                    refine ⟨891453421950291325840829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377209125200776868908877 891453421950291325840829)
                    ·
                      rfl

theorem cell22_2604149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2604149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604149 prefixEnd_2604149 := by exact prefixLift 2604149
  have htrace : WordTrace (prefixWord ++ tailWord_2604149) baseStart_2604149 baseEnd_2604149 := by
    simpa [prefixWord, tailWord_2604149, baseEnd_2604149] using wordTrace_append hprefix tailTrace_2604149
  have hstable : (prefixWord ++ tailWord_2604149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604149).length < 2 ^ (prefixWord ++ tailWord_2604149).sum := by decide
  have hdescent : baseEnd_2604149 < baseStart_2604149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604194 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2604194 : Nat := 118140960795 + 2604194 * 2 ^ 59
def prefixEnd_2604194 : Nat := 4983230072969 + 3 ^ 40 * 2604194 * 2
def baseEnd_2604194 : Nat := 891468826369926208465691

theorem tailTrace_2604194 : CollatzResearch.WordTrace tailWord_2604194 prefixEnd_2604194 891468826369926208465691 := by
  unfold tailWord_2604194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23745689581864343442770909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63321838884971582514055757 23745689581864343442770909)
  ·
    refine ⟨8904633593199128791039091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23745689581864343442770909 8904633593199128791039091)
    ·
      refine ⟨13356950389798693186558637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904633593199128791039091 13356950389798693186558637)
      ·
        refine ⟨5008856396174509944959489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13356950389798693186558637 5008856396174509944959489)
        ·
          refine ⟨3756642297130882458719617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5008856396174509944959489 3756642297130882458719617)
          ·
            refine ⟨2817481722848161844039713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3756642297130882458719617 2817481722848161844039713)
            ·
              refine ⟨2113111292136121383029785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2817481722848161844039713 2113111292136121383029785)
              ·
                refine ⟨1584833469102091037272339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113111292136121383029785 1584833469102091037272339)
                ·
                  refine ⟨2377250203653136555908509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584833469102091037272339 2377250203653136555908509)
                  ·
                    refine ⟨891468826369926208465691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377250203653136555908509 891468826369926208465691)
                    ·
                      rfl

theorem cell22_2604194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2604194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604194 prefixEnd_2604194 := by exact prefixLift 2604194
  have htrace : WordTrace (prefixWord ++ tailWord_2604194) baseStart_2604194 baseEnd_2604194 := by
    simpa [prefixWord, tailWord_2604194, baseEnd_2604194] using wordTrace_append hprefix tailTrace_2604194
  have hstable : (prefixWord ++ tailWord_2604194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604194).length < 2 ^ (prefixWord ++ tailWord_2604194).sum := by decide
  have hdescent : baseEnd_2604194 < baseStart_2604194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604237 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2604237 : Nat := 118140960795 + 2604237 * 2 ^ 59
def prefixEnd_2604237 : Nat := 4983230072969 + 3 ^ 40 * 2604237 * 2
def baseEnd_2604237 : Nat := 891483546148688429640559

theorem tailTrace_2604237 : CollatzResearch.WordTrace tailWord_2604237 prefixEnd_2604237 891483546148688429640559 := by
  unfold tailWord_2604237
  simp only [CollatzResearch.WordTrace]
  refine ⟨94984326666301592114898965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63322884444201061409932643 94984326666301592114898965)
  ·
    refine ⟨4452390312482887130385889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94984326666301592114898965 4452390312482887130385889)
    ·
      refine ⟨3339292734362165347789417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4452390312482887130385889 3339292734362165347789417)
      ·
        refine ⟨2504469550771624010842063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3339292734362165347789417 2504469550771624010842063)
        ·
          refine ⟨3756704326157436016263095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504469550771624010842063 3756704326157436016263095)
          ·
            refine ⟨5635056489236154024394643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756704326157436016263095 5635056489236154024394643)
            ·
              refine ⟨8452584733854231036591965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635056489236154024394643 8452584733854231036591965)
              ·
                refine ⟨3169719275195336638721987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8452584733854231036591965 3169719275195336638721987)
                ·
                  refine ⟨4754578912793004958082981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169719275195336638721987 4754578912793004958082981)
                  ·
                    refine ⟨891483546148688429640559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754578912793004958082981 891483546148688429640559)
                    ·
                      rfl

theorem cell22_2604237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2604237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604237 prefixEnd_2604237 := by exact prefixLift 2604237
  have htrace : WordTrace (prefixWord ++ tailWord_2604237) baseStart_2604237 baseEnd_2604237 := by
    simpa [prefixWord, tailWord_2604237, baseEnd_2604237] using wordTrace_append hprefix tailTrace_2604237
  have hstable : (prefixWord ++ tailWord_2604237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604237).length < 2 ^ (prefixWord ++ tailWord_2604237).sum := by decide
  have hdescent : baseEnd_2604237 < baseStart_2604237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_2604304 : Nat := 118140960795 + 2604304 * 2 ^ 59
def prefixEnd_2604304 : Nat := 4983230072969 + 3 ^ 40 * 2604304 * 2
def baseEnd_2604304 : Nat := 891506481617922588215353

theorem tailTrace_2604304 : CollatzResearch.WordTrace tailWord_2604304 prefixEnd_2604304 891506481617922588215353 := by
  unfold tailWord_2604304
  simp only [CollatzResearch.WordTrace]
  refine ⟨47493385178529431278793983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63324513571372575038391977 47493385178529431278793983)
  ·
    refine ⟨71240077767794146918190975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47493385178529431278793983 71240077767794146918190975)
    ·
      refine ⟨106860116651691220377286463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71240077767794146918190975 106860116651691220377286463)
      ·
        refine ⟨160290174977536830565929695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106860116651691220377286463 160290174977536830565929695)
        ·
          refine ⟨240435262466305245848894543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160290174977536830565929695 240435262466305245848894543)
          ·
            refine ⟨360652893699457868773341815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240435262466305245848894543 360652893699457868773341815)
            ·
              refine ⟨540979340549186803160012723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360652893699457868773341815 540979340549186803160012723)
              ·
                refine ⟨811469010823780204740019085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540979340549186803160012723 811469010823780204740019085)
                ·
                  refine ⟨304300879058917576777507157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811469010823780204740019085 304300879058917576777507157)
                  ·
                    refine ⟨891506481617922588215353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 304300879058917576777507157 891506481617922588215353)
                    ·
                      rfl

theorem cell22_2604304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_2604304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604304 prefixEnd_2604304 := by exact prefixLift 2604304
  have htrace : WordTrace (prefixWord ++ tailWord_2604304) baseStart_2604304 baseEnd_2604304 := by
    simpa [prefixWord, tailWord_2604304, baseEnd_2604304] using wordTrace_append hprefix tailTrace_2604304
  have hstable : (prefixWord ++ tailWord_2604304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604304).length < 2 ^ (prefixWord ++ tailWord_2604304).sum := by decide
  have hdescent : baseEnd_2604304 < baseStart_2604304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604312 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 1, 3]
def baseStart_2604312 : Nat := 118140960795 + 2604312 * 2 ^ 59
def prefixEnd_2604312 : Nat := 4983230072969 + 3 ^ 40 * 2604312 * 2
def baseEnd_2604312 : Nat := 891509220181413234015329

theorem tailTrace_2604312 : CollatzResearch.WordTrace tailWord_2604312 prefixEnd_2604312 891509220181413234015329 := by
  unfold tailWord_2604312
  simp only [CollatzResearch.WordTrace]
  refine ⟨47493531070514939961939595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63324708094019919949252793 47493531070514939961939595)
  ·
    refine ⟨71240296605772409942909393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47493531070514939961939595 71240296605772409942909393)
    ·
      refine ⟨53430222454329307457182045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71240296605772409942909393 53430222454329307457182045)
      ·
        refine ⟨20036333420373490296443267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53430222454329307457182045 20036333420373490296443267)
        ·
          refine ⟨30054500130560235444664901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20036333420373490296443267 30054500130560235444664901)
          ·
            refine ⟨5635218774480044145874669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30054500130560235444664901 5635218774480044145874669)
            ·
              refine ⟨2113207040430016554703001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5635218774480044145874669 2113207040430016554703001)
              ·
                refine ⟨1584905280322512416027251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113207040430016554703001 1584905280322512416027251)
                ·
                  refine ⟨2377357920483768624040877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584905280322512416027251 2377357920483768624040877)
                  ·
                    refine ⟨891509220181413234015329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377357920483768624040877 891509220181413234015329)
                    ·
                      rfl

theorem cell22_2604312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_2604312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604312 prefixEnd_2604312 := by exact prefixLift 2604312
  have htrace : WordTrace (prefixWord ++ tailWord_2604312) baseStart_2604312 baseEnd_2604312 := by
    simpa [prefixWord, tailWord_2604312, baseEnd_2604312] using wordTrace_append hprefix tailTrace_2604312
  have hstable : (prefixWord ++ tailWord_2604312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604312).length < 2 ^ (prefixWord ++ tailWord_2604312).sum := by decide
  have hdescent : baseEnd_2604312 < baseStart_2604312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604321 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2604321 : Nat := 118140960795 + 2604321 * 2 ^ 59
def prefixEnd_2604321 : Nat := 4983230072969 + 3 ^ 40 * 2604321 * 2
def baseEnd_2604321 : Nat := 891512301065340210540301

theorem tailTrace_2604321 : CollatzResearch.WordTrace tailWord_2604321 prefixEnd_2604321 891512301065340210540301 := by
  unfold tailWord_2604321
  simp only [CollatzResearch.WordTrace]
  refine ⟨94987390397997274460956817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63324926931998182973971211 94987390397997274460956817)
  ·
    refine ⟨71240542798497955845717613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94987390397997274460956817 71240542798497955845717613)
    ·
      refine ⟨26715203549436733442144105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71240542798497955845717613 26715203549436733442144105)
      ·
        refine ⟨20036402662077550081608079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26715203549436733442144105 20036402662077550081608079)
        ·
          refine ⟨30054603993116325122412119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20036402662077550081608079 30054603993116325122412119)
          ·
            refine ⟨45081905989674487683618179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30054603993116325122412119 45081905989674487683618179)
            ·
              refine ⟨67622858984511731525427269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45081905989674487683618179 67622858984511731525427269)
              ·
                refine ⟨12679286059595949661017613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67622858984511731525427269 12679286059595949661017613)
                ·
                  refine ⟨4754732272348481122881605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12679286059595949661017613 4754732272348481122881605)
                  ·
                    refine ⟨891512301065340210540301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754732272348481122881605 891512301065340210540301)
                    ·
                      rfl

theorem cell22_2604321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2604321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604321 prefixEnd_2604321 := by exact prefixLift 2604321
  have htrace : WordTrace (prefixWord ++ tailWord_2604321) baseStart_2604321 baseEnd_2604321 := by
    simpa [prefixWord, tailWord_2604321, baseEnd_2604321] using wordTrace_append hprefix tailTrace_2604321
  have hstable : (prefixWord ++ tailWord_2604321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604321).length < 2 ^ (prefixWord ++ tailWord_2604321).sum := by decide
  have hdescent : baseEnd_2604321 < baseStart_2604321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604325 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 5]
def baseStart_2604325 : Nat := 118140960795 + 2604325 * 2 ^ 59
def prefixEnd_2604325 : Nat := 4983230072969 + 3 ^ 40 * 2604325 * 2
def baseEnd_2604325 : Nat := 297171223449028511146763

theorem tailTrace_2604325 : CollatzResearch.WordTrace tailWord_2604325 prefixEnd_2604325 297171223449028511146763 := by
  unfold tailWord_2604325
  simp only [CollatzResearch.WordTrace]
  refine ⟨94987536289982783144102429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63325024193321855429401619 94987536289982783144102429)
  ·
    refine ⟨35620326108743543679038411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94987536289982783144102429 35620326108743543679038411)
    ·
      refine ⟨53430489163115315518557617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35620326108743543679038411 53430489163115315518557617)
      ·
        refine ⟨40072866872336486638918213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53430489163115315518557617 40072866872336486638918213)
        ·
          refine ⟨7513662538563091244797165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40072866872336486638918213 7513662538563091244797165)
          ·
            refine ⟨2817623451961159216798937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7513662538563091244797165 2817623451961159216798937)
            ·
              refine ⟨2113217588970869412599203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2817623451961159216798937 2113217588970869412599203)
              ·
                refine ⟨3169826383456304118898805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113217588970869412599203 3169826383456304118898805)
                ·
                  refine ⟨297171223449028511146763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3169826383456304118898805 297171223449028511146763)
                  ·
                    rfl

theorem cell22_2604325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_2604325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604325 prefixEnd_2604325 := by exact prefixLift 2604325
  have htrace : WordTrace (prefixWord ++ tailWord_2604325) baseStart_2604325 baseEnd_2604325 := by
    simpa [prefixWord, tailWord_2604325, baseEnd_2604325] using wordTrace_append hprefix tailTrace_2604325
  have hstable : (prefixWord ++ tailWord_2604325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604325).length < 2 ^ (prefixWord ++ tailWord_2604325).sum := by decide
  have hdescent : baseEnd_2604325 < baseStart_2604325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604338 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2604338 : Nat := 118140960795 + 2604338 * 2 ^ 59
def prefixEnd_2604338 : Nat := 4983230072969 + 3 ^ 40 * 2604338 * 2
def baseEnd_2604338 : Nat := 891518120512757832865249

theorem tailTrace_2604338 : CollatzResearch.WordTrace tailWord_2604338 prefixEnd_2604338 891518120512757832865249 := by
  unfold tailWord_2604338
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747002609733921591081417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63325340292623790909550445 23747002609733921591081417)
  ·
    refine ⟨17810251957300441193311063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23747002609733921591081417 17810251957300441193311063)
    ·
      refine ⟨26715377935950661789966595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17810251957300441193311063 26715377935950661789966595)
      ·
        refine ⟨40073066903925992684949893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26715377935950661789966595 40073066903925992684949893)
        ·
          refine ⟨7513700044486123628428105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40073066903925992684949893 7513700044486123628428105)
          ·
            refine ⟨5635275033364592721321079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7513700044486123628428105 5635275033364592721321079)
            ·
              refine ⟨8452912550046889081981619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635275033364592721321079 8452912550046889081981619)
              ·
                refine ⟨12679368825070333622972429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8452912550046889081981619 12679368825070333622972429)
                ·
                  refine ⟨4754763309401375108614661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12679368825070333622972429 4754763309401375108614661)
                  ·
                    refine ⟨891518120512757832865249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4754763309401375108614661 891518120512757832865249)
                    ·
                      rfl

theorem cell22_2604338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2604338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604338 prefixEnd_2604338 := by exact prefixLift 2604338
  have htrace : WordTrace (prefixWord ++ tailWord_2604338) baseStart_2604338 baseEnd_2604338 := by
    simpa [prefixWord, tailWord_2604338, baseEnd_2604338] using wordTrace_append hprefix tailTrace_2604338
  have hstable : (prefixWord ++ tailWord_2604338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604338).length < 2 ^ (prefixWord ++ tailWord_2604338).sum := by decide
  have hdescent : baseEnd_2604338 < baseStart_2604338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604351 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_2604351 : Nat := 118140960795 + 2604351 * 2 ^ 59
def prefixEnd_2604351 : Nat := 4983230072969 + 3 ^ 40 * 2604351 * 2
def baseEnd_2604351 : Nat := 891522570678430132290209

theorem tailTrace_2604351 : CollatzResearch.WordTrace tailWord_2604351 prefixEnd_2604351 891522570678430132290209 := by
  unfold tailWord_2604351
  simp only [CollatzResearch.WordTrace]
  refine ⟨94988484587888589584548907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63325656391925726389699271 94988484587888589584548907)
  ·
    refine ⟨142482726881832884376823361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94988484587888589584548907 142482726881832884376823361)
    ·
      refine ⟨106862045161374663282617521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142482726881832884376823361 106862045161374663282617521)
      ·
        refine ⟨80146533871030997461963141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106862045161374663282617521 80146533871030997461963141)
        ·
          refine ⟨15027475100818312024118089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80146533871030997461963141 15027475100818312024118089)
          ·
            refine ⟨11270606325613734018088567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15027475100818312024118089 11270606325613734018088567)
            ·
              refine ⟨16905909488420601027132851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11270606325613734018088567 16905909488420601027132851)
              ·
                refine ⟨25358864232630901540699277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16905909488420601027132851 25358864232630901540699277)
                ·
                  refine ⟨9509574087236588077762229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25358864232630901540699277 9509574087236588077762229)
                  ·
                    refine ⟨891522570678430132290209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9509574087236588077762229 891522570678430132290209)
                    ·
                      rfl

theorem cell22_2604351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_2604351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604351 prefixEnd_2604351 := by exact prefixLift 2604351
  have htrace : WordTrace (prefixWord ++ tailWord_2604351) baseStart_2604351 baseEnd_2604351 := by
    simpa [prefixWord, tailWord_2604351, baseEnd_2604351] using wordTrace_append hprefix tailTrace_2604351
  have hstable : (prefixWord ++ tailWord_2604351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604351).length < 2 ^ (prefixWord ++ tailWord_2604351).sum := by decide
  have hdescent : baseEnd_2604351 < baseStart_2604351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604374 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2604374 : Nat := 118140960795 + 2604374 * 2 ^ 59
def prefixEnd_2604374 : Nat := 4983230072969 + 3 ^ 40 * 2604374 * 2
def baseEnd_2604374 : Nat := 891530444048465738965139

theorem tailTrace_2604374 : CollatzResearch.WordTrace tailWord_2604374 prefixEnd_2604374 891530444048465738965139 := by
  unfold tailWord_2604374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936832716675329032039761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63326215644536843008424117 5936832716675329032039761)
  ·
    refine ⟨4452624537506496774029821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5936832716675329032039761 4452624537506496774029821)
    ·
      refine ⟨1669734201564936290261183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4452624537506496774029821 1669734201564936290261183)
      ·
        refine ⟨2504601302347404435391775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669734201564936290261183 2504601302347404435391775)
        ·
          refine ⟨3756901953521106653087663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504601302347404435391775 3756901953521106653087663)
          ·
            refine ⟨5635352930281659979631495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756901953521106653087663 5635352930281659979631495)
            ·
              refine ⟨8453029395422489969447243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635352930281659979631495 8453029395422489969447243)
              ·
                refine ⟨12679544093133734954170865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8453029395422489969447243 12679544093133734954170865)
                ·
                  refine ⟨9509658069850301215628149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12679544093133734954170865 9509658069850301215628149)
                  ·
                    refine ⟨891530444048465738965139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9509658069850301215628149 891530444048465738965139)
                    ·
                      rfl

theorem cell22_2604374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2604374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604374 prefixEnd_2604374 := by exact prefixLift 2604374
  have htrace : WordTrace (prefixWord ++ tailWord_2604374) baseStart_2604374 baseEnd_2604374 := by
    simpa [prefixWord, tailWord_2604374, baseEnd_2604374] using wordTrace_append hprefix tailTrace_2604374
  have hstable : (prefixWord ++ tailWord_2604374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604374).length < 2 ^ (prefixWord ++ tailWord_2604374).sum := by decide
  have hdescent : baseEnd_2604374 < baseStart_2604374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604413 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_2604413 : Nat := 118140960795 + 2604413 * 2 ^ 59
def prefixEnd_2604413 : Nat := 4983230072969 + 3 ^ 40 * 2604413 * 2
def baseEnd_2604413 : Nat := 891543794545482637240019

theorem tailTrace_2604413 : CollatzResearch.WordTrace tailWord_2604413 prefixEnd_2604413 891543794545482637240019 := by
  unfold tailWord_2604413
  simp only [CollatzResearch.WordTrace]
  refine ⟨94990745913663974173305893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63327163942442649448870595 94990745913663974173305893)
  ·
    refine ⟨17810764858811995157494855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94990745913663974173305893 17810764858811995157494855)
    ·
      refine ⟨26716147288217992736242283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17810764858811995157494855 26716147288217992736242283)
      ·
        refine ⟨40074220932326989104363425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26716147288217992736242283 40074220932326989104363425)
        ·
          refine ⟨30055665699245241828272569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40074220932326989104363425 30055665699245241828272569)
          ·
            refine ⟨22541749274433931371204427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30055665699245241828272569 22541749274433931371204427)
            ·
              refine ⟨33812623911650897056806641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22541749274433931371204427 33812623911650897056806641)
              ·
                refine ⟨25359467933738172792604981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33812623911650897056806641 25359467933738172792604981)
                ·
                  refine ⟨2377450118787953699306717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25359467933738172792604981 2377450118787953699306717)
                  ·
                    refine ⟨891543794545482637240019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377450118787953699306717 891543794545482637240019)
                    ·
                      rfl

theorem cell22_2604413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_2604413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604413 prefixEnd_2604413 := by exact prefixLift 2604413
  have htrace : WordTrace (prefixWord ++ tailWord_2604413) baseStart_2604413 baseEnd_2604413 := by
    simpa [prefixWord, tailWord_2604413, baseEnd_2604413] using wordTrace_append hprefix tailTrace_2604413
  have hstable : (prefixWord ++ tailWord_2604413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604413).length < 2 ^ (prefixWord ++ tailWord_2604413).sum := by decide
  have hdescent : baseEnd_2604413 < baseStart_2604413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604565 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2604565 : Nat := 118140960795 + 2604565 * 2 ^ 59
def prefixEnd_2604565 : Nat := 4983230072969 + 3 ^ 40 * 2604565 * 2
def baseEnd_2604565 : Nat := 891595827251804907439553

theorem tailTrace_2604565 : CollatzResearch.WordTrace tailWord_2604565 prefixEnd_2604565 891595827251804907439553 := by
  unfold tailWord_2604565
  simp only [CollatzResearch.WordTrace]
  refine ⟨94996289809113304132839149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63330859872742202755226099 94996289809113304132839149)
  ·
    refine ⟨35623608678417489049814681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94996289809113304132839149 35623608678417489049814681)
    ·
      refine ⟨26717706508813116787361011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35623608678417489049814681 26717706508813116787361011)
      ·
        refine ⟨40076559763219675181041517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26717706508813116787361011 40076559763219675181041517)
        ·
          refine ⟨15028709911207378192890569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40076559763219675181041517 15028709911207378192890569)
          ·
            refine ⟨11271532433405533644667927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15028709911207378192890569 11271532433405533644667927)
            ·
              refine ⟨16907298650108300467001891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11271532433405533644667927 16907298650108300467001891)
              ·
                refine ⟨25360947975162450700502837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16907298650108300467001891 25360947975162450700502837)
                ·
                  refine ⟨2377588872671479753172141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25360947975162450700502837 2377588872671479753172141)
                  ·
                    refine ⟨891595827251804907439553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377588872671479753172141 891595827251804907439553)
                    ·
                      rfl

theorem cell22_2604565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2604565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604565 prefixEnd_2604565 := by exact prefixLift 2604565
  have htrace : WordTrace (prefixWord ++ tailWord_2604565) baseStart_2604565 baseEnd_2604565 := by
    simpa [prefixWord, tailWord_2604565, baseEnd_2604565] using wordTrace_append hprefix tailTrace_2604565
  have hstable : (prefixWord ++ tailWord_2604565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604565).length < 2 ^ (prefixWord ++ tailWord_2604565).sum := by decide
  have hdescent : baseEnd_2604565 < baseStart_2604565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
