import V185TrunkScan23Chunk0965

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5718637 : List Nat := [1, 5, 1, 1, 3, 2, 1, 9]
def baseStart_5718637 : Nat := 118140960795 + 5718637 * 2 ^ 59
def prefixEnd_5718637 : Nat := 4983230072969 + 3 ^ 40 * 5718637 * 2
def baseEnd_5718637 : Nat := 108755906280949908893999

theorem tailTrace_5718637 : CollatzResearch.WordTrace tailWord_5718637 prefixEnd_5718637 108755906280949908893999 := by
  unfold tailWord_5718637
  simp only [CollatzResearch.WordTrace]
  refine ⟨208575826583362289288402165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139050551055574859525601443 208575826583362289288402165)
  ·
    refine ⟨19553983742190214620787703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208575826583362289288402165 19553983742190214620787703)
    ·
      refine ⟨29330975613285321931181555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553983742190214620787703 29330975613285321931181555)
      ·
        refine ⟨43996463419927982896772333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29330975613285321931181555 43996463419927982896772333)
        ·
          refine ⟨16498673782472993586289625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43996463419927982896772333 16498673782472993586289625)
          ·
            refine ⟨12374005336854745189717219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16498673782472993586289625 12374005336854745189717219)
            ·
              refine ⟨18561008005282117784575829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12374005336854745189717219 18561008005282117784575829)
              ·
                refine ⟨108755906280949908893999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18561008005282117784575829 108755906280949908893999)
                ·
                  rfl

theorem cell23_5718637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 9].length) (baseStart_5718637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718637 prefixEnd_5718637 := by exact prefixLift 5718637
  have htrace : WordTrace (prefixWord ++ tailWord_5718637) baseStart_5718637 baseEnd_5718637 := by
    simpa [prefixWord, tailWord_5718637, baseEnd_5718637] using wordTrace_append hprefix tailTrace_5718637
  have hstable : (prefixWord ++ tailWord_5718637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718637).length < 2 ^ (prefixWord ++ tailWord_5718637).sum := by decide
  have hdescent : baseEnd_5718637 < baseStart_5718637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718647 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_5718647 : Nat := 118140960795 + 5718647 * 2 ^ 59
def prefixEnd_5718647 : Nat := 4983230072969 + 3 ^ 40 * 5718647 * 2
def baseEnd_5718647 : Nat := 2936414604392192501012927

theorem tailTrace_5718647 : CollatzResearch.WordTrace tailWord_5718647 prefixEnd_5718647 2936414604392192501012927 := by
  unfold tailWord_5718647
  simp only [CollatzResearch.WordTrace]
  refine ⟨208576191313326060996266195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139050794208884040664177463 208576191313326060996266195)
  ·
    refine ⟨312864286969989091494399293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208576191313326060996266195 312864286969989091494399293)
    ·
      refine ⟨117324107613745909310399735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312864286969989091494399293 117324107613745909310399735)
      ·
        refine ⟨175986161420618863965599603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117324107613745909310399735 175986161420618863965599603)
        ·
          refine ⟨263979242130928295948399405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175986161420618863965599603 263979242130928295948399405)
          ·
            refine ⟨98992215799098110980649777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263979242130928295948399405 98992215799098110980649777)
            ·
              refine ⟨74244161849323583235487333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98992215799098110980649777 74244161849323583235487333)
              ·
                refine ⟨13920780346748171856653875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74244161849323583235487333 13920780346748171856653875)
                ·
                  refine ⟨20881170520122257784980813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13920780346748171856653875 20881170520122257784980813)
                  ·
                    refine ⟨7830438945045846669367805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20881170520122257784980813 7830438945045846669367805)
                    ·
                      refine ⟨2936414604392192501012927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830438945045846669367805 2936414604392192501012927)
                      ·
                        rfl

theorem cell23_5718647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_5718647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718647 prefixEnd_5718647 := by exact prefixLift 5718647
  have htrace : WordTrace (prefixWord ++ tailWord_5718647) baseStart_5718647 baseEnd_5718647 := by
    simpa [prefixWord, tailWord_5718647, baseEnd_5718647] using wordTrace_append hprefix tailTrace_5718647
  have hstable : (prefixWord ++ tailWord_5718647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718647).length < 2 ^ (prefixWord ++ tailWord_5718647).sum := by decide
  have hdescent : baseEnd_5718647 < baseStart_5718647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718698 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5718698 : Nat := 118140960795 + 5718698 * 2 ^ 59
def prefixEnd_5718698 : Nat := 4983230072969 + 3 ^ 40 * 5718698 * 2
def baseEnd_5718698 : Nat := 2936440791905571801475193

theorem tailTrace_5718698 : CollatzResearch.WordTrace tailWord_5718698 prefixEnd_5718698 2936440791905571801475193 := by
  unfold tailWord_5718698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52144512859035324176593187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139052034290760864470915165 52144512859035324176593187)
  ·
    refine ⟨78216769288552986264889781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52144512859035324176593187 78216769288552986264889781)
    ·
      refine ⟨7332822120801842462333417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78216769288552986264889781 7332822120801842462333417)
      ·
        refine ⟨5499616590601381846750063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7332822120801842462333417 5499616590601381846750063)
        ·
          refine ⟨8249424885902072770125095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499616590601381846750063 8249424885902072770125095)
          ·
            refine ⟨12374137328853109155187643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8249424885902072770125095 12374137328853109155187643)
            ·
              refine ⟨18561205993279663732781465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12374137328853109155187643 18561205993279663732781465)
              ·
                refine ⟨13920904494959747799586099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18561205993279663732781465 13920904494959747799586099)
                ·
                  refine ⟨20881356742439621699379149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13920904494959747799586099 20881356742439621699379149)
                  ·
                    refine ⟨7830508778414858137267181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20881356742439621699379149 7830508778414858137267181)
                    ·
                      refine ⟨2936440791905571801475193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830508778414858137267181 2936440791905571801475193)
                      ·
                        rfl

theorem cell23_5718698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5718698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718698 prefixEnd_5718698 := by exact prefixLift 5718698
  have htrace : WordTrace (prefixWord ++ tailWord_5718698) baseStart_5718698 baseEnd_5718698 := by
    simpa [prefixWord, tailWord_5718698, baseEnd_5718698] using wordTrace_append hprefix tailTrace_5718698
  have hstable : (prefixWord ++ tailWord_5718698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718698).length < 2 ^ (prefixWord ++ tailWord_5718698).sum := by decide
  have hdescent : baseEnd_5718698 < baseStart_5718698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718707 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5]
def baseStart_5718707 : Nat := 118140960795 + 5718707 * 2 ^ 59
def prefixEnd_5718707 : Nat := 4983230072969 + 3 ^ 40 * 5718707 * 2
def baseEnd_5718707 : Nat := 2936445413231462266262651

theorem tailTrace_5718707 : CollatzResearch.WordTrace tailWord_5718707 prefixEnd_5718707 2936445413231462266262651 := by
  unfold tailWord_5718707
  simp only [CollatzResearch.WordTrace]
  refine ⟨208578379693108691243450375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139052253128739127495633583 208578379693108691243450375)
  ·
    refine ⟨312867569539663036865175563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208578379693108691243450375 312867569539663036865175563)
    ·
      refine ⟨469301354309494555297763345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312867569539663036865175563 469301354309494555297763345)
      ·
        refine ⟨351976015732120916473322509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469301354309494555297763345 351976015732120916473322509)
        ·
          refine ⟨131991005899545343677495941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351976015732120916473322509 131991005899545343677495941)
          ·
            refine ⟨24748313606164751939530489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131991005899545343677495941 24748313606164751939530489)
            ·
              refine ⟨18561235204623563954647867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24748313606164751939530489 18561235204623563954647867)
              ·
                refine ⟨27841852806935345931971801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18561235204623563954647867 27841852806935345931971801)
                ·
                  refine ⟨20881389605201509448978851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27841852806935345931971801 20881389605201509448978851)
                  ·
                    refine ⟨31322084407802264173468277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20881389605201509448978851 31322084407802264173468277)
                    ·
                      refine ⟨2936445413231462266262651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31322084407802264173468277 2936445413231462266262651)
                      ·
                        rfl

theorem cell23_5718707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_5718707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718707 prefixEnd_5718707 := by exact prefixLift 5718707
  have htrace : WordTrace (prefixWord ++ tailWord_5718707) baseStart_5718707 baseEnd_5718707 := by
    simpa [prefixWord, tailWord_5718707, baseEnd_5718707] using wordTrace_append hprefix tailTrace_5718707
  have hstable : (prefixWord ++ tailWord_5718707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718707).length < 2 ^ (prefixWord ++ tailWord_5718707).sum := by decide
  have hdescent : baseEnd_5718707 < baseStart_5718707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718724 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_5718724 : Nat := 118140960795 + 5718724 * 2 ^ 59
def prefixEnd_5718724 : Nat := 4983230072969 + 3 ^ 40 * 5718724 * 2
def baseEnd_5718724 : Nat := 2936454142402588699750073

theorem tailTrace_5718724 : CollatzResearch.WordTrace tailWord_5718724 prefixEnd_5718724 2936454142402588699750073 := by
  unfold tailWord_5718724
  simp only [CollatzResearch.WordTrace]
  refine ⟨104289499867023551573409613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139052666489364735431212817 104289499867023551573409613)
  ·
    refine ⟨39108562450133831840028605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104289499867023551573409613 39108562450133831840028605)
    ·
      refine ⟨14665710918800186940010727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39108562450133831840028605 14665710918800186940010727)
      ·
        refine ⟨21998566378200280410016091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14665710918800186940010727 21998566378200280410016091)
        ·
          refine ⟨32997849567300420615024137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21998566378200280410016091 32997849567300420615024137)
          ·
            refine ⟨24748387175475315461268103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32997849567300420615024137 24748387175475315461268103)
            ·
              refine ⟨37122580763212973191902155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24748387175475315461268103 37122580763212973191902155)
              ·
                refine ⟨55683871144819459787853233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37122580763212973191902155 55683871144819459787853233)
                ·
                  refine ⟨41762903358614594840889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55683871144819459787853233 41762903358614594840889925)
                  ·
                    refine ⟨7830544379740236532666861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41762903358614594840889925 7830544379740236532666861)
                    ·
                      refine ⟨2936454142402588699750073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830544379740236532666861 2936454142402588699750073)
                      ·
                        rfl

theorem cell23_5718724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_5718724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718724 prefixEnd_5718724 := by exact prefixLift 5718724
  have htrace : WordTrace (prefixWord ++ tailWord_5718724) baseStart_5718724 baseEnd_5718724 := by
    simpa [prefixWord, tailWord_5718724, baseEnd_5718724] using wordTrace_append hprefix tailTrace_5718724
  have hstable : (prefixWord ++ tailWord_5718724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718724).length < 2 ^ (prefixWord ++ tailWord_5718724).sum := by decide
  have hdescent : baseEnd_5718724 < baseStart_5718724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718734 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_5718734 : Nat := 118140960795 + 5718734 * 2 ^ 59
def prefixEnd_5718734 : Nat := 4983230072969 + 3 ^ 40 * 5718734 * 2
def baseEnd_5718734 : Nat := 2936459277209133660625027

theorem tailTrace_5718734 : CollatzResearch.WordTrace tailWord_5718734 prefixEnd_5718734 2936459277209133660625027 := by
  unfold tailWord_5718734
  simp only [CollatzResearch.WordTrace]
  refine ⟨26072420558001359356835407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139052909642673916569788837 26072420558001359356835407)
  ·
    refine ⟨39108630837002039035253111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26072420558001359356835407 39108630837002039035253111)
    ·
      refine ⟨58662946255503058552879667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39108630837002039035253111 58662946255503058552879667)
      ·
        refine ⟨87994419383254587829319501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58662946255503058552879667 87994419383254587829319501)
        ·
          refine ⟨32997907268720470435994813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87994419383254587829319501 32997907268720470435994813)
          ·
            refine ⟨12374215225770176413498055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32997907268720470435994813 12374215225770176413498055)
            ·
              refine ⟨18561322838655264620247083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12374215225770176413498055 18561322838655264620247083)
              ·
                refine ⟨27841984257982896930370625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18561322838655264620247083 27841984257982896930370625)
                ·
                  refine ⟨20881488193487172697777969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27841984257982896930370625 20881488193487172697777969)
                  ·
                    refine ⟨15661116145115379523333477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20881488193487172697777969 15661116145115379523333477)
                    ·
                      refine ⟨2936459277209133660625027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15661116145115379523333477 2936459277209133660625027)
                      ·
                        rfl

theorem cell23_5718734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_5718734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718734 prefixEnd_5718734 := by exact prefixLift 5718734
  have htrace : WordTrace (prefixWord ++ tailWord_5718734) baseStart_5718734 baseEnd_5718734 := by
    simpa [prefixWord, tailWord_5718734, baseEnd_5718734] using wordTrace_append hprefix tailTrace_5718734
  have hstable : (prefixWord ++ tailWord_5718734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718734).length < 2 ^ (prefixWord ++ tailWord_5718734).sum := by decide
  have hdescent : baseEnd_5718734 < baseStart_5718734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718738 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_5718738 : Nat := 118140960795 + 5718738 * 2 ^ 59
def prefixEnd_5718738 : Nat := 4983230072969 + 3 ^ 40 * 5718738 * 2
def baseEnd_5718738 : Nat := 2936461331131751644975009

theorem tailTrace_5718738 : CollatzResearch.WordTrace tailWord_5718738 prefixEnd_5718738 2936461331131751644975009 := by
  unfold tailWord_5718738
  simp only [CollatzResearch.WordTrace]
  refine ⟨52144877588999095884457217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139053006903997589025219245 52144877588999095884457217)
  ·
    refine ⟨39108658191749321913342913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52144877588999095884457217 39108658191749321913342913)
    ·
      refine ⟨29331493643811991435007185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39108658191749321913342913 29331493643811991435007185)
      ·
        refine ⟨21998620232858993576255389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29331493643811991435007185 21998620232858993576255389)
        ·
          refine ⟨8249482587322122591095771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21998620232858993576255389 8249482587322122591095771)
          ·
            refine ⟨12374223880983183886643657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8249482587322122591095771 12374223880983183886643657)
            ·
              refine ⟨9280667910737387914982743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12374223880983183886643657 9280667910737387914982743)
              ·
                refine ⟨13921001866106081872474115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9280667910737387914982743 13921001866106081872474115)
                ·
                  refine ⟨20881502799159122808711173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13921001866106081872474115 20881502799159122808711173)
                  ·
                    refine ⟨3915281774842335526633345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20881502799159122808711173 3915281774842335526633345)
                    ·
                      refine ⟨2936461331131751644975009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3915281774842335526633345 2936461331131751644975009)
                      ·
                        rfl

theorem cell23_5718738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_5718738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718738 prefixEnd_5718738 := by exact prefixLift 5718738
  have htrace : WordTrace (prefixWord ++ tailWord_5718738) baseStart_5718738 baseEnd_5718738 := by
    simpa [prefixWord, tailWord_5718738, baseEnd_5718738] using wordTrace_append hprefix tailTrace_5718738
  have hstable : (prefixWord ++ tailWord_5718738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718738).length < 2 ^ (prefixWord ++ tailWord_5718738).sum := by decide
  have hdescent : baseEnd_5718738 < baseStart_5718738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718772 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5718772 : Nat := 118140960795 + 5718772 * 2 ^ 59
def prefixEnd_5718772 : Nat := 4983230072969 + 3 ^ 40 * 5718772 * 2
def baseEnd_5718772 : Nat := 2936478789474004511949853

theorem tailTrace_5718772 : CollatzResearch.WordTrace tailWord_5718772 prefixEnd_5718772 2936478789474004511949853 := by
  unfold tailWord_5718772
  simp only [CollatzResearch.WordTrace]
  refine ⟨104290375218936603672283285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139053833625248804896377713 104290375218936603672283285)
  ·
    refine ⟨4888611338387653297138279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104290375218936603672283285 4888611338387653297138279)
    ·
      refine ⟨7332917007581479945707419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888611338387653297138279 7332917007581479945707419)
      ·
        refine ⟨10999375511372219918561129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7332917007581479945707419 10999375511372219918561129)
        ·
          refine ⟨8249531633529164938920847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10999375511372219918561129 8249531633529164938920847)
          ·
            refine ⟨12374297450293747408381271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8249531633529164938920847 12374297450293747408381271)
            ·
              refine ⟨18561446175440621112571907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12374297450293747408381271 18561446175440621112571907)
              ·
                refine ⟨27842169263160931668857861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18561446175440621112571907 27842169263160931668857861)
                ·
                  refine ⟨5220406736842674687910849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27842169263160931668857861 5220406736842674687910849)
                  ·
                    refine ⟨3915305052632006015933137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5220406736842674687910849 3915305052632006015933137)
                    ·
                      refine ⟨2936478789474004511949853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3915305052632006015933137 2936478789474004511949853)
                      ·
                        rfl

theorem cell23_5718772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5718772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718772 prefixEnd_5718772 := by exact prefixLift 5718772
  have htrace : WordTrace (prefixWord ++ tailWord_5718772) baseStart_5718772 baseEnd_5718772 := by
    simpa [prefixWord, tailWord_5718772, baseEnd_5718772] using wordTrace_append hprefix tailTrace_5718772
  have hstable : (prefixWord ++ tailWord_5718772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718772).length < 2 ^ (prefixWord ++ tailWord_5718772).sum := by decide
  have hdescent : baseEnd_5718772 < baseStart_5718772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718774 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_5718774 : Nat := 118140960795 + 5718774 * 2 ^ 59
def prefixEnd_5718774 : Nat := 4983230072969 + 3 ^ 40 * 5718774 * 2
def baseEnd_5718774 : Nat := 978826605478437834708281

theorem tailTrace_5718774 : CollatzResearch.WordTrace tailWord_5718774 prefixEnd_5718774 978826605478437834708281 := by
  unfold tailWord_5718774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036301461491622605383711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139053882255910641124092917 13036301461491622605383711)
  ·
    refine ⟨19554452192237433908075567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13036301461491622605383711 19554452192237433908075567)
    ·
      refine ⟨29331678288356150862113351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19554452192237433908075567 29331678288356150862113351)
      ·
        refine ⟨43997517432534226293170027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29331678288356150862113351 43997517432534226293170027)
        ·
          refine ⟨65996276148801339439755041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43997517432534226293170027 65996276148801339439755041)
          ·
            refine ⟨49497207111601004579816281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65996276148801339439755041 49497207111601004579816281)
            ·
              refine ⟨37122905333700753434862211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49497207111601004579816281 37122905333700753434862211)
              ·
                refine ⟨55684358000551130152293317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37122905333700753434862211 55684358000551130152293317)
                ·
                  refine ⟨10440817125103336903554997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55684358000551130152293317 10440817125103336903554997)
                  ·
                    refine ⟨978826605478437834708281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10440817125103336903554997 978826605478437834708281)
                    ·
                      rfl

theorem cell23_5718774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_5718774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718774 prefixEnd_5718774 := by exact prefixLift 5718774
  have htrace : WordTrace (prefixWord ++ tailWord_5718774) baseStart_5718774 baseEnd_5718774 := by
    simpa [prefixWord, tailWord_5718774, baseEnd_5718774] using wordTrace_append hprefix tailTrace_5718774
  have hstable : (prefixWord ++ tailWord_5718774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718774).length < 2 ^ (prefixWord ++ tailWord_5718774).sum := by decide
  have hdescent : baseEnd_5718774 < baseStart_5718774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718817 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 10]
def baseStart_5718817 : Nat := 118140960795 + 5718817 * 2 ^ 59
def prefixEnd_5718817 : Nat := 4983230072969 + 3 ^ 40 * 5718817 * 2
def baseEnd_5718817 : Nat := 326277988455939648431905

theorem tailTrace_5718817 : CollatzResearch.WordTrace tailWord_5718817 prefixEnd_5718817 326277988455939648431905 := by
  unfold tailWord_5718817
  simp only [CollatzResearch.WordTrace]
  refine ⟨208582391722710180029954705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139054927815140120019969803 208582391722710180029954705)
  ·
    refine ⟨156436793792032635022466029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208582391722710180029954705 156436793792032635022466029)
    ·
      refine ⟨58663797672012238133424761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156436793792032635022466029 58663797672012238133424761)
      ·
        refine ⟨43997848254009178600068571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58663797672012238133424761 43997848254009178600068571)
        ·
          refine ⟨65996772381013767900102857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43997848254009178600068571 65996772381013767900102857)
          ·
            refine ⟨49497579285760325925077143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65996772381013767900102857 49497579285760325925077143)
            ·
              refine ⟨74246368928640488887615715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49497579285760325925077143 74246368928640488887615715)
              ·
                refine ⟨111369553392960733331423573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74246368928640488887615715 111369553392960733331423573)
                ·
                  refine ⟨326277988455939648431905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111369553392960733331423573 326277988455939648431905)
                  ·
                    rfl

theorem cell23_5718817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_5718817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718817 prefixEnd_5718817 := by exact prefixLift 5718817
  have htrace : WordTrace (prefixWord ++ tailWord_5718817) baseStart_5718817 baseEnd_5718817 := by
    simpa [prefixWord, tailWord_5718817, baseEnd_5718817] using wordTrace_append hprefix tailTrace_5718817
  have hstable : (prefixWord ++ tailWord_5718817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718817).length < 2 ^ (prefixWord ++ tailWord_5718817).sum := by decide
  have hdescent : baseEnd_5718817 < baseStart_5718817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718834 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_5718834 : Nat := 118140960795 + 5718834 * 2 ^ 59
def prefixEnd_5718834 : Nat := 4983230072969 + 3 ^ 40 * 5718834 * 2
def baseEnd_5718834 : Nat := 326278958363842585486063

theorem tailTrace_5718834 : CollatzResearch.WordTrace tailWord_5718834 prefixEnd_5718834 326278958363842585486063 := by
  unfold tailWord_5718834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52145752940912147983330889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139055341175765727955549037 52145752940912147983330889)
  ·
    refine ⟨39109314705684110987498167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52145752940912147983330889 39109314705684110987498167)
    ·
      refine ⟨58663972058526166481247251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39109314705684110987498167 58663972058526166481247251)
      ·
        refine ⟨87995958087789249721870877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58663972058526166481247251 87995958087789249721870877)
        ·
          refine ⟨32998484282920968645701579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87995958087789249721870877 32998484282920968645701579)
          ·
            refine ⟨49497726424381452968552369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32998484282920968645701579 49497726424381452968552369)
            ·
              refine ⟨37123294818286089726414277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49497726424381452968552369 37123294818286089726414277)
              ·
                refine ⟨6960617778428641823702677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37123294818286089726414277 6960617778428641823702677)
                ·
                  refine ⟨326278958363842585486063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6960617778428641823702677 326278958363842585486063)
                  ·
                    rfl

theorem cell23_5718834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_5718834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718834 prefixEnd_5718834 := by exact prefixLift 5718834
  have htrace : WordTrace (prefixWord ++ tailWord_5718834) baseStart_5718834 baseEnd_5718834 := by
    simpa [prefixWord, tailWord_5718834, baseEnd_5718834] using wordTrace_append hprefix tailTrace_5718834
  have hstable : (prefixWord ++ tailWord_5718834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718834).length < 2 ^ (prefixWord ++ tailWord_5718834).sum := by decide
  have hdescent : baseEnd_5718834 < baseStart_5718834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718888 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5718888 : Nat := 118140960795 + 5718888 * 2 ^ 59
def prefixEnd_5718888 : Nat := 4983230072969 + 3 ^ 40 * 5718888 * 2
def baseEnd_5718888 : Nat := 2936538353229926058099319

theorem tailTrace_5718888 : CollatzResearch.WordTrace tailWord_5718888 prefixEnd_5718888 2936538353229926058099319 := by
  unfold tailWord_5718888
  simp only [CollatzResearch.WordTrace]
  refine ⟨104292490652726479577894659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139056654203635306103859545 104292490652726479577894659)
  ·
    refine ⟨156438735979089719366841989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104292490652726479577894659 156438735979089719366841989)
    ·
      refine ⟨29332262996079322381282873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156438735979089719366841989 29332262996079322381282873)
      ·
        refine ⟨21999197247059491785962155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29332262996079322381282873 21999197247059491785962155)
        ·
          refine ⟨32998795870589237678943233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21999197247059491785962155 32998795870589237678943233)
          ·
            refine ⟨24749096902941928259207425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32998795870589237678943233 24749096902941928259207425)
            ·
              refine ⟨18561822677206446194405569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24749096902941928259207425 18561822677206446194405569)
              ·
                refine ⟨13921367007904834645804177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18561822677206446194405569 13921367007904834645804177)
                ·
                  refine ⟨10441025255928625984353133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13921367007904834645804177 10441025255928625984353133)
                  ·
                    refine ⟨3915384470973234744132425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10441025255928625984353133 3915384470973234744132425)
                    ·
                      refine ⟨2936538353229926058099319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3915384470973234744132425 2936538353229926058099319)
                      ·
                        rfl

theorem cell23_5718888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5718888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718888 prefixEnd_5718888 := by exact prefixLift 5718888
  have htrace : WordTrace (prefixWord ++ tailWord_5718888) baseStart_5718888 baseEnd_5718888 := by
    simpa [prefixWord, tailWord_5718888, baseEnd_5718888] using wordTrace_append hprefix tailTrace_5718888
  have hstable : (prefixWord ++ tailWord_5718888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718888).length < 2 ^ (prefixWord ++ tailWord_5718888).sum := by decide
  have hdescent : baseEnd_5718888 < baseStart_5718888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718901 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5718901 : Nat := 118140960795 + 5718901 * 2 ^ 59
def prefixEnd_5718901 : Nat := 4983230072969 + 3 ^ 40 * 5718901 * 2
def baseEnd_5718901 : Nat := 2936545028478434507236759

theorem tailTrace_5718901 : CollatzResearch.WordTrace tailWord_5718901 prefixEnd_5718901 2936545028478434507236759 := by
  unfold tailWord_5718901
  simp only [CollatzResearch.WordTrace]
  refine ⟨208585455454405862376012557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139056970302937241584008371 208585455454405862376012557)
  ·
    refine ⟨78219545795402198391004709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208585455454405862376012557 78219545795402198391004709)
    ·
      refine ⟨14666164836637912198313383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78219545795402198391004709 14666164836637912198313383)
      ·
        refine ⟨21999247254956868297470075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14666164836637912198313383 21999247254956868297470075)
        ·
          refine ⟨32998870882435302446205113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21999247254956868297470075 32998870882435302446205113)
          ·
            refine ⟨24749153161826476834653835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32998870882435302446205113 24749153161826476834653835)
            ·
              refine ⟨37123729742739715251980753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24749153161826476834653835 37123729742739715251980753)
              ·
                refine ⟨27842797307054786438985565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37123729742739715251980753 27842797307054786438985565)
                ·
                  refine ⟨10441048990145544914619587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27842797307054786438985565 10441048990145544914619587)
                  ·
                    refine ⟨15661573485218317371929381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10441048990145544914619587 15661573485218317371929381)
                    ·
                      refine ⟨2936545028478434507236759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15661573485218317371929381 2936545028478434507236759)
                      ·
                        rfl

theorem cell23_5718901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5718901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718901 prefixEnd_5718901 := by exact prefixLift 5718901
  have htrace : WordTrace (prefixWord ++ tailWord_5718901) baseStart_5718901 baseEnd_5718901 := by
    simpa [prefixWord, tailWord_5718901, baseEnd_5718901] using wordTrace_append hprefix tailTrace_5718901
  have hstable : (prefixWord ++ tailWord_5718901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718901).length < 2 ^ (prefixWord ++ tailWord_5718901).sum := by decide
  have hdescent : baseEnd_5718901 < baseStart_5718901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718911 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 2, 4]
def baseStart_5718911 : Nat := 118140960795 + 5718911 * 2 ^ 59
def prefixEnd_5718911 : Nat := 4983230072969 + 3 ^ 40 * 5718911 * 2
def baseEnd_5718911 : Nat := 978850054428326489370571

theorem tailTrace_5718911 : CollatzResearch.WordTrace tailWord_5718911 prefixEnd_5718911 978850054428326489370571 := by
  unfold tailWord_5718911
  simp only [CollatzResearch.WordTrace]
  refine ⟨208585820184369634083876587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139057213456246422722584391 208585820184369634083876587)
  ·
    refine ⟨312878730276554451125814881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208585820184369634083876587 312878730276554451125814881)
    ·
      refine ⟨234659047707415838344361161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312878730276554451125814881 234659047707415838344361161)
      ·
        refine ⟨175994285780561878758270871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234659047707415838344361161 175994285780561878758270871)
        ·
          refine ⟨263991428670842818137406307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175994285780561878758270871 263991428670842818137406307)
          ·
            refine ⟨395987143006264227206109461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263991428670842818137406307 395987143006264227206109461)
            ·
              refine ⟨18561897328418635650286381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 395987143006264227206109461 18561897328418635650286381)
              ·
                refine ⟨6960711498156988368857393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18561897328418635650286381 6960711498156988368857393)
                ·
                  refine ⟨5220533623617741276643045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6960711498156988368857393 5220533623617741276643045)
                  ·
                    refine ⟨978850054428326489370571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220533623617741276643045 978850054428326489370571)
                    ·
                      rfl

theorem cell23_5718911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_5718911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718911 prefixEnd_5718911 := by exact prefixLift 5718911
  have htrace : WordTrace (prefixWord ++ tailWord_5718911) baseStart_5718911 baseEnd_5718911 := by
    simpa [prefixWord, tailWord_5718911, baseEnd_5718911] using wordTrace_append hprefix tailTrace_5718911
  have hstable : (prefixWord ++ tailWord_5718911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718911).length < 2 ^ (prefixWord ++ tailWord_5718911).sum := by decide
  have hdescent : baseEnd_5718911 < baseStart_5718911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718921 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_5718921 : Nat := 118140960795 + 5718921 * 2 ^ 59
def prefixEnd_5718921 : Nat := 4983230072969 + 3 ^ 40 * 5718921 * 2
def baseEnd_5718921 : Nat := 2936555298091524428986667

theorem tailTrace_5718921 : CollatzResearch.WordTrace tailWord_5718921 prefixEnd_5718921 2936555298091524428986667 := by
  unfold tailWord_5718921
  simp only [CollatzResearch.WordTrace]
  refine ⟨208586184914333405791740617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139057456609555603861160411 208586184914333405791740617)
  ·
    refine ⟨156439638685750054343805463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208586184914333405791740617 156439638685750054343805463)
    ·
      refine ⟨234659458028625081515708195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156439638685750054343805463 234659458028625081515708195)
      ·
        refine ⟨351989187042937622273562293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234659458028625081515708195 351989187042937622273562293)
        ·
          refine ⟨32998986285275402088146465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351989187042937622273562293 32998986285275402088146465)
          ·
            refine ⟨24749239713956551566109849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32998986285275402088146465 24749239713956551566109849)
            ·
              refine ⟨18561929785467413674582387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24749239713956551566109849 18561929785467413674582387)
              ·
                refine ⟨27842894678201120511873581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18561929785467413674582387 27842894678201120511873581)
                ·
                  refine ⟨10441085504325420191952593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27842894678201120511873581 10441085504325420191952593)
                  ·
                    refine ⟨7830814128244065143964445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10441085504325420191952593 7830814128244065143964445)
                    ·
                      refine ⟨2936555298091524428986667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830814128244065143964445 2936555298091524428986667)
                      ·
                        rfl

theorem cell23_5718921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_5718921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718921 prefixEnd_5718921 := by exact prefixLift 5718921
  have htrace : WordTrace (prefixWord ++ tailWord_5718921) baseStart_5718921 baseEnd_5718921 := by
    simpa [prefixWord, tailWord_5718921, baseEnd_5718921] using wordTrace_append hprefix tailTrace_5718921
  have hstable : (prefixWord ++ tailWord_5718921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718921).length < 2 ^ (prefixWord ++ tailWord_5718921).sum := by decide
  have hdescent : baseEnd_5718921 < baseStart_5718921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718945 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 2, 4]
def baseStart_5718945 : Nat := 118140960795 + 5718945 * 2 ^ 59
def prefixEnd_5718945 : Nat := 4983230072969 + 3 ^ 40 * 5718945 * 2
def baseEnd_5718945 : Nat := 978855873875744111695519

theorem tailTrace_5718945 : CollatzResearch.WordTrace tailWord_5718945 prefixEnd_5718945 978855873875744111695519 := by
  unfold tailWord_5718945
  simp only [CollatzResearch.WordTrace]
  refine ⟨208587060266246457890614289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139058040177497638593742859 208587060266246457890614289)
  ·
    refine ⟨156440295199684843417960717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208587060266246457890614289 156440295199684843417960717)
    ·
      refine ⟨58665110699881816281735269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156440295199684843417960717 58665110699881816281735269)
      ·
        refine ⟨10999708256227840552825363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58665110699881816281735269 10999708256227840552825363)
        ·
          refine ⟨16499562384341760829238045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10999708256227840552825363 16499562384341760829238045)
          ·
            refine ⟨6187335894128160310964267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16499562384341760829238045 6187335894128160310964267)
            ·
              refine ⟨9281003841192240466446401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6187335894128160310964267 9281003841192240466446401)
              ·
                refine ⟨6960752880894180349834801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9281003841192240466446401 6960752880894180349834801)
                ·
                  refine ⟨5220564660670635262376101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6960752880894180349834801 5220564660670635262376101)
                  ·
                    refine ⟨978855873875744111695519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220564660670635262376101 978855873875744111695519)
                    ·
                      rfl

theorem cell23_5718945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_5718945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718945 prefixEnd_5718945 := by exact prefixLift 5718945
  have htrace : WordTrace (prefixWord ++ tailWord_5718945) baseStart_5718945 baseEnd_5718945 := by
    simpa [prefixWord, tailWord_5718945, baseEnd_5718945] using wordTrace_append hprefix tailTrace_5718945
  have hstable : (prefixWord ++ tailWord_5718945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718945).length < 2 ^ (prefixWord ++ tailWord_5718945).sum := by decide
  have hdescent : baseEnd_5718945 < baseStart_5718945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718968 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_5718968 : Nat := 118140960795 + 5718968 * 2 ^ 59
def prefixEnd_5718968 : Nat := 4983230072969 + 3 ^ 40 * 5718968 * 2
def baseEnd_5718968 : Nat := 2936579431682285745098951

theorem tailTrace_5718968 : CollatzResearch.WordTrace tailWord_5718968 prefixEnd_5718968 2936579431682285745098951 := by
  unfold tailWord_5718968
  simp only [CollatzResearch.WordTrace]
  refine ⟨104293949572581566409350779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139058599430108755212467705 104293949572581566409350779)
  ·
    refine ⟨156440924358872349614026169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104293949572581566409350779 156440924358872349614026169)
    ·
      refine ⟨117330693269154262210519627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156440924358872349614026169 117330693269154262210519627)
      ·
        refine ⟨175996039903731393315779441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117330693269154262210519627 175996039903731393315779441)
        ·
          refine ⟨131997029927798544986834581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175996039903731393315779441 131997029927798544986834581)
          ·
            refine ⟨6187360777865556796257871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131997029927798544986834581 6187360777865556796257871)
            ·
              refine ⟨9281041166798335194386807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6187360777865556796257871 9281041166798335194386807)
              ·
                refine ⟨13921561750197502791580211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9281041166798335194386807 13921561750197502791580211)
                ·
                  refine ⟨20882342625296254187370317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13921561750197502791580211 20882342625296254187370317)
                  ·
                    refine ⟨7830878484486095320263869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20882342625296254187370317 7830878484486095320263869)
                    ·
                      refine ⟨2936579431682285745098951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830878484486095320263869 2936579431682285745098951)
                      ·
                        rfl

theorem cell23_5718968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_5718968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718968 prefixEnd_5718968 := by exact prefixLift 5718968
  have htrace : WordTrace (prefixWord ++ tailWord_5718968) baseStart_5718968 baseEnd_5718968 := by
    simpa [prefixWord, tailWord_5718968, baseEnd_5718968] using wordTrace_append hprefix tailTrace_5718968
  have hstable : (prefixWord ++ tailWord_5718968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718968).length < 2 ^ (prefixWord ++ tailWord_5718968).sum := by decide
  have hdescent : baseEnd_5718968 < baseStart_5718968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719011 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5719011 : Nat := 118140960795 + 5719011 * 2 ^ 59
def prefixEnd_5719011 : Nat := 4983230072969 + 3 ^ 40 * 5719011 * 2
def baseEnd_5719011 : Nat := 2936601511350429076861253

theorem tailTrace_5719011 : CollatzResearch.WordTrace tailWord_5719011 prefixEnd_5719011 2936601511350429076861253 := by
  unfold tailWord_5719011
  simp only [CollatzResearch.WordTrace]
  refine ⟨208589467484007351162516887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139059644989338234108344591 208589467484007351162516887)
  ·
    refine ⟨312884201226011026743775331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208589467484007351162516887 312884201226011026743775331)
    ·
      refine ⟨469326301839016540115662997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312884201226011026743775331 469326301839016540115662997)
      ·
        refine ⟨21999670398703900317921703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 469326301839016540115662997 21999670398703900317921703)
        ·
          refine ⟨32999505598055850476882555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21999670398703900317921703 32999505598055850476882555)
          ·
            refine ⟨49499258397083775715323833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32999505598055850476882555 49499258397083775715323833)
            ·
              refine ⟨37124443797812831786492875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49499258397083775715323833 37124443797812831786492875)
              ·
                refine ⟨55686665696719247679739313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37124443797812831786492875 55686665696719247679739313)
                ·
                  refine ⟨41764999272539435759804485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55686665696719247679739313 41764999272539435759804485)
                  ·
                    refine ⟨7830937363601144204963341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41764999272539435759804485 7830937363601144204963341)
                    ·
                      refine ⟨2936601511350429076861253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830937363601144204963341 2936601511350429076861253)
                      ·
                        rfl

theorem cell23_5719011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5719011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719011 prefixEnd_5719011 := by exact prefixLift 5719011
  have htrace : WordTrace (prefixWord ++ tailWord_5719011) baseStart_5719011 baseEnd_5719011 := by
    simpa [prefixWord, tailWord_5719011, baseEnd_5719011] using wordTrace_append hprefix tailTrace_5719011
  have hstable : (prefixWord ++ tailWord_5719011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719011).length < 2 ^ (prefixWord ++ tailWord_5719011).sum := by decide
  have hdescent : baseEnd_5719011 < baseStart_5719011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719034 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_5719034 : Nat := 118140960795 + 5719034 * 2 ^ 59
def prefixEnd_5719034 : Nat := 4983230072969 + 3 ^ 40 * 5719034 * 2
def baseEnd_5719034 : Nat := 2936613321405482486873647

theorem tailTrace_5719034 : CollatzResearch.WordTrace tailWord_5719034 prefixEnd_5719034 2936613321405482486873647 := by
  unfold tailWord_5719034
  simp only [CollatzResearch.WordTrace]
  refine ⟨52147576590731006522651039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139060204241949350727069437 52147576590731006522651039)
  ·
    refine ⟨78221364886096509783976559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52147576590731006522651039 78221364886096509783976559)
    ·
      refine ⟨117332047329144764675964839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78221364886096509783976559 117332047329144764675964839)
      ·
        refine ⟨175998070993717147013947259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117332047329144764675964839 175998070993717147013947259)
        ·
          refine ⟨263997106490575720520920889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175998070993717147013947259 263997106490575720520920889)
          ·
            refine ⟨197997829867931790390690667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263997106490575720520920889 197997829867931790390690667)
            ·
              refine ⟨296996744801897685586036001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197997829867931790390690667 296996744801897685586036001)
              ·
                refine ⟨222747558601423264189527001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296996744801897685586036001 222747558601423264189527001)
                ·
                  refine ⟨167060668951067448142145251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222747558601423264189527001 167060668951067448142145251)
                  ·
                    refine ⟨250591003426601172213217877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167060668951067448142145251 250591003426601172213217877)
                    ·
                      refine ⟨2936613321405482486873647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250591003426601172213217877 2936613321405482486873647)
                      ·
                        rfl

theorem cell23_5719034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_5719034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719034 prefixEnd_5719034 := by exact prefixLift 5719034
  have htrace : WordTrace (prefixWord ++ tailWord_5719034) baseStart_5719034 baseEnd_5719034 := by
    simpa [prefixWord, tailWord_5719034, baseEnd_5719034] using wordTrace_append hprefix tailTrace_5719034
  have hstable : (prefixWord ++ tailWord_5719034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719034).length < 2 ^ (prefixWord ++ tailWord_5719034).sum := by decide
  have hdescent : baseEnd_5719034 < baseStart_5719034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719071 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_5719071 : Nat := 118140960795 + 5719071 * 2 ^ 59
def prefixEnd_5719071 : Nat := 4983230072969 + 3 ^ 40 * 5719071 * 2
def baseEnd_5719071 : Nat := 2936632320189698842110977

theorem tailTrace_5719071 : CollatzResearch.WordTrace tailWord_5719071 prefixEnd_5719071 2936632320189698842110977 := by
  unfold tailWord_5719071
  simp only [CollatzResearch.WordTrace]
  refine ⟨208591655863789981409701067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139061103909193320939800711 208591655863789981409701067)
  ·
    refine ⟨312887483795684972114551601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208591655863789981409701067 312887483795684972114551601)
    ·
      refine ⟨234665612846763729085913701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312887483795684972114551601 234665612846763729085913701)
      ·
        refine ⟨43999802408768199203608819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234665612846763729085913701 43999802408768199203608819)
        ·
          refine ⟨65999703613152298805413229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43999802408768199203608819 65999703613152298805413229)
          ·
            refine ⟨24749888854932112052029961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65999703613152298805413229 24749888854932112052029961)
            ·
              refine ⟨18562416641199084039022471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24749888854932112052029961 18562416641199084039022471)
              ·
                refine ⟨27843624961798626058533707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18562416641199084039022471 27843624961798626058533707)
                ·
                  refine ⟨41765437442697939087800561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27843624961798626058533707 41765437442697939087800561)
                  ·
                    refine ⟨31324078082023454315850421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41765437442697939087800561 31324078082023454315850421)
                    ·
                      refine ⟨2936632320189698842110977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31324078082023454315850421 2936632320189698842110977)
                      ·
                        rfl

theorem cell23_5719071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_5719071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719071 prefixEnd_5719071 := by exact prefixLift 5719071
  have htrace : WordTrace (prefixWord ++ tailWord_5719071) baseStart_5719071 baseEnd_5719071 := by
    simpa [prefixWord, tailWord_5719071, baseEnd_5719071] using wordTrace_append hprefix tailTrace_5719071
  have hstable : (prefixWord ++ tailWord_5719071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719071).length < 2 ^ (prefixWord ++ tailWord_5719071).sum := by decide
  have hdescent : baseEnd_5719071 < baseStart_5719071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719098 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_5719098 : Nat := 118140960795 + 5719098 * 2 ^ 59
def prefixEnd_5719098 : Nat := 4983230072969 + 3 ^ 40 * 5719098 * 2
def baseEnd_5719098 : Nat := 2936646184167370236473353

theorem tailTrace_5719098 : CollatzResearch.WordTrace tailWord_5719098 prefixEnd_5719098 2936646184167370236473353 := by
  unfold tailWord_5719098
  simp only [CollatzResearch.WordTrace]
  refine ⟨52148160158673041255233487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139061760423128110013955965 52148160158673041255233487)
  ·
    refine ⟨78222240238009561882850231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52148160158673041255233487 78222240238009561882850231)
    ·
      refine ⟨117333360357014342824275347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78222240238009561882850231 117333360357014342824275347)
      ·
        refine ⟨176000040535521514236413021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117333360357014342824275347 176000040535521514236413021)
        ·
          refine ⟨66000015200820567838654883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176000040535521514236413021 66000015200820567838654883)
          ·
            refine ⟨99000022801230851757982325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66000015200820567838654883 99000022801230851757982325)
            ·
              refine ⟨9281252137615392352310843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99000022801230851757982325 9281252137615392352310843)
              ·
                refine ⟨13921878206423088528466265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9281252137615392352310843 13921878206423088528466265)
                ·
                  refine ⟨10441408654817316396349699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13921878206423088528466265 10441408654817316396349699)
                  ·
                    refine ⟨15662112982225974594524549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10441408654817316396349699 15662112982225974594524549)
                    ·
                      refine ⟨2936646184167370236473353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15662112982225974594524549 2936646184167370236473353)
                      ·
                        rfl

theorem cell23_5719098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_5719098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719098 prefixEnd_5719098 := by exact prefixLift 5719098
  have htrace : WordTrace (prefixWord ++ tailWord_5719098) baseStart_5719098 baseEnd_5719098 := by
    simpa [prefixWord, tailWord_5719098, baseEnd_5719098] using wordTrace_append hprefix tailTrace_5719098
  have hstable : (prefixWord ++ tailWord_5719098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719098).length < 2 ^ (prefixWord ++ tailWord_5719098).sum := by decide
  have hdescent : baseEnd_5719098 < baseStart_5719098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719111 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_5719111 : Nat := 118140960795 + 5719111 * 2 ^ 59
def prefixEnd_5719111 : Nat := 4983230072969 + 3 ^ 40 * 5719111 * 2
def baseEnd_5719111 : Nat := 2936652859415878685610793

theorem tailTrace_5719111 : CollatzResearch.WordTrace tailWord_5719111 prefixEnd_5719111 2936652859415878685610793 := by
  unfold tailWord_5719111
  simp only [CollatzResearch.WordTrace]
  refine ⟨208593114783645068241157187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139062076522430045494104791 208593114783645068241157187)
  ·
    refine ⟨312889672175467602361735781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208593114783645068241157187 312889672175467602361735781)
    ·
      refine ⟨58666813532900175442825459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312889672175467602361735781 58666813532900175442825459)
      ·
        refine ⟨88000220299350263164238189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58666813532900175442825459 88000220299350263164238189)
        ·
          refine ⟨33000082612256348686589321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88000220299350263164238189 33000082612256348686589321)
          ·
            refine ⟨24750061959192261514941991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33000082612256348686589321 24750061959192261514941991)
            ·
              refine ⟨37125092938788392272412987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24750061959192261514941991 37125092938788392272412987)
              ·
                refine ⟨55687639408182588408619481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37125092938788392272412987 55687639408182588408619481)
                ·
                  refine ⟨41765729556136941306464611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55687639408182588408619481 41765729556136941306464611)
                  ·
                    refine ⟨62648594334205411959696917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41765729556136941306464611 62648594334205411959696917)
                    ·
                      refine ⟨2936652859415878685610793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62648594334205411959696917 2936652859415878685610793)
                      ·
                        rfl

theorem cell23_5719111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_5719111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719111 prefixEnd_5719111 := by exact prefixLift 5719111
  have htrace : WordTrace (prefixWord ++ tailWord_5719111) baseStart_5719111 baseEnd_5719111 := by
    simpa [prefixWord, tailWord_5719111, baseEnd_5719111] using wordTrace_append hprefix tailTrace_5719111
  have hstable : (prefixWord ++ tailWord_5719111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719111).length < 2 ^ (prefixWord ++ tailWord_5719111).sum := by decide
  have hdescent : baseEnd_5719111 < baseStart_5719111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719118 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_5719118 : Nat := 118140960795 + 5719118 * 2 ^ 59
def prefixEnd_5719118 : Nat := 4983230072969 + 3 ^ 40 * 5719118 * 2
def baseEnd_5719118 : Nat := 2936656453780460158223261

theorem tailTrace_5719118 : CollatzResearch.WordTrace tailWord_5719118 prefixEnd_5719118 2936656453780460158223261 := by
  unfold tailWord_5719118
  simp only [CollatzResearch.WordTrace]
  refine ⟨26074171261827463554582751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139062246729746472291108005 26074171261827463554582751)
  ·
    refine ⟨39111256892741195331874127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26074171261827463554582751 39111256892741195331874127)
    ·
      refine ⟨58666885339111792997811191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39111256892741195331874127 58666885339111792997811191)
      ·
        refine ⟨88000328008667689496716787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58666885339111792997811191 88000328008667689496716787)
        ·
          refine ⟨132000492013001534245075181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88000328008667689496716787 132000492013001534245075181)
          ·
            refine ⟨49500184504875575341903193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132000492013001534245075181 49500184504875575341903193)
            ·
              refine ⟨37125138378656681506427395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49500184504875575341903193 37125138378656681506427395)
              ·
                refine ⟨55687707567985022259641093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37125138378656681506427395 55687707567985022259641093)
                ·
                  refine ⟨10441445168997191673682705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55687707567985022259641093 10441445168997191673682705)
                  ·
                    refine ⟨7831083876747893755262029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10441445168997191673682705 7831083876747893755262029)
                    ·
                      refine ⟨2936656453780460158223261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7831083876747893755262029 2936656453780460158223261)
                      ·
                        rfl

theorem cell23_5719118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_5719118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719118 prefixEnd_5719118 := by exact prefixLift 5719118
  have htrace : WordTrace (prefixWord ++ tailWord_5719118) baseStart_5719118 baseEnd_5719118 := by
    simpa [prefixWord, tailWord_5719118, baseEnd_5719118] using wordTrace_append hprefix tailTrace_5719118
  have hstable : (prefixWord ++ tailWord_5719118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719118).length < 2 ^ (prefixWord ++ tailWord_5719118).sum := by decide
  have hdescent : baseEnd_5719118 < baseStart_5719118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719125 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_5719125 : Nat := 118140960795 + 5719125 * 2 ^ 59
def prefixEnd_5719125 : Nat := 4983230072969 + 3 ^ 40 * 5719125 * 2
def baseEnd_5719125 : Nat := 978886682715013876945243

theorem tailTrace_5719125 : CollatzResearch.WordTrace tailWord_5719125 prefixEnd_5719125 978886682715013876945243 := by
  unfold tailWord_5719125
  simp only [CollatzResearch.WordTrace]
  refine ⟨208593625405594348632166829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139062416937062899088111219 208593625405594348632166829)
  ·
    refine ⟨78222609527097880737062561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208593625405594348632166829 78222609527097880737062561)
    ·
      refine ⟨58666957145323410552796921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78222609527097880737062561 58666957145323410552796921)
      ·
        refine ⟨44000217858992557914597691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58666957145323410552796921 44000217858992557914597691)
        ·
          refine ⟨66000326788488836871896537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44000217858992557914597691 66000326788488836871896537)
          ·
            refine ⟨49500245091366627653922403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66000326788488836871896537 49500245091366627653922403)
            ·
              refine ⟨74250367637049941480883605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49500245091366627653922403 74250367637049941480883605)
              ·
                refine ⟨3480485982986716006916419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74250367637049941480883605 3480485982986716006916419)
                ·
                  refine ⟨5220728974480074010374629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480485982986716006916419 5220728974480074010374629)
                  ·
                    refine ⟨978886682715013876945243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220728974480074010374629 978886682715013876945243)
                    ·
                      rfl

theorem cell23_5719125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_5719125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719125 prefixEnd_5719125 := by exact prefixLift 5719125
  have htrace : WordTrace (prefixWord ++ tailWord_5719125) baseStart_5719125 baseEnd_5719125 := by
    simpa [prefixWord, tailWord_5719125, baseEnd_5719125] using wordTrace_append hprefix tailTrace_5719125
  have hstable : (prefixWord ++ tailWord_5719125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719125).length < 2 ^ (prefixWord ++ tailWord_5719125).sum := by decide
  have hdescent : baseEnd_5719125 < baseStart_5719125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719141 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_5719141 : Nat := 118140960795 + 5719141 * 2 ^ 59
def prefixEnd_5719141 : Nat := 4983230072969 + 3 ^ 40 * 5719141 * 2
def baseEnd_5719141 : Nat := 2936668263835513568235655

theorem tailTrace_5719141 : CollatzResearch.WordTrace tailWord_5719141 prefixEnd_5719141 2936668263835513568235655 := by
  unfold tailWord_5719141
  simp only [CollatzResearch.WordTrace]
  refine ⟨208594208973536383364749277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139062805982357588909832851 208594208973536383364749277)
  ·
    refine ⟨78222828365076143761780979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208594208973536383364749277 78222828365076143761780979)
    ·
      refine ⟨117334242547614215642671469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78222828365076143761780979 117334242547614215642671469)
      ·
        refine ⟨44000340955355330866001801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117334242547614215642671469 44000340955355330866001801)
        ·
          refine ⟨33000255716516498149501351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44000340955355330866001801 33000255716516498149501351)
          ·
            refine ⟨49500383574774747224252027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33000255716516498149501351 49500383574774747224252027)
            ·
              refine ⟨74250575362162120836378041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49500383574774747224252027 74250575362162120836378041)
              ·
                refine ⟨55687931521621590627283531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74250575362162120836378041 55687931521621590627283531)
                ·
                  refine ⟨83531897282432385940925297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55687931521621590627283531 83531897282432385940925297)
                  ·
                    refine ⟨62648922961824289455693973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83531897282432385940925297 62648922961824289455693973)
                    ·
                      refine ⟨2936668263835513568235655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62648922961824289455693973 2936668263835513568235655)
                      ·
                        rfl

theorem cell23_5719141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_5719141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719141 prefixEnd_5719141 := by exact prefixLift 5719141
  have htrace : WordTrace (prefixWord ++ tailWord_5719141) baseStart_5719141 baseEnd_5719141 := by
    simpa [prefixWord, tailWord_5719141, baseEnd_5719141] using wordTrace_append hprefix tailTrace_5719141
  have hstable : (prefixWord ++ tailWord_5719141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719141).length < 2 ^ (prefixWord ++ tailWord_5719141).sum := by decide
  have hdescent : baseEnd_5719141 < baseStart_5719141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719168 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 1, 5]
def baseStart_5719168 : Nat := 118140960795 + 5719168 * 2 ^ 59
def prefixEnd_5719168 : Nat := 4983230072969 + 3 ^ 40 * 5719168 * 2
def baseEnd_5719168 : Nat := 978894042604394987532677

theorem tailTrace_5719168 : CollatzResearch.WordTrace tailWord_5719168 prefixEnd_5719168 978894042604394987532677 := by
  unfold tailWord_5719168
  simp only [CollatzResearch.WordTrace]
  refine ⟨104297596872219283487991079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139063462496292377983988105 104297596872219283487991079)
  ·
    refine ⟨156446395308328925231986619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104297596872219283487991079 156446395308328925231986619)
    ·
      refine ⟨234669592962493387847979929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156446395308328925231986619 234669592962493387847979929)
      ·
        refine ⟨176002194721870040885984947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234669592962493387847979929 176002194721870040885984947)
        ·
          refine ⟨264003292082805061328977421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176002194721870040885984947 264003292082805061328977421)
          ·
            refine ⟨99001234531051897998366533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264003292082805061328977421 99001234531051897998366533)
            ·
              refine ⟨18562731474572230874693725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99001234531051897998366533 18562731474572230874693725)
              ·
                refine ⟨6961024302964586578010147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18562731474572230874693725 6961024302964586578010147)
                ·
                  refine ⟨10441536454446879867015221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961024302964586578010147 10441536454446879867015221)
                  ·
                    refine ⟨978894042604394987532677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10441536454446879867015221 978894042604394987532677)
                    ·
                      rfl

theorem cell23_5719168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_5719168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719168 prefixEnd_5719168 := by exact prefixLift 5719168
  have htrace : WordTrace (prefixWord ++ tailWord_5719168) baseStart_5719168 baseEnd_5719168 := by
    simpa [prefixWord, tailWord_5719168, baseEnd_5719168] using wordTrace_append hprefix tailTrace_5719168
  have hstable : (prefixWord ++ tailWord_5719168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719168).length < 2 ^ (prefixWord ++ tailWord_5719168).sum := by decide
  have hdescent : baseEnd_5719168 < baseStart_5719168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719182 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5719182 : Nat := 118140960795 + 5719182 * 2 ^ 59
def prefixEnd_5719182 : Nat := 4983230072969 + 3 ^ 40 * 5719182 * 2
def baseEnd_5719182 : Nat := 2936689316542347907822967

theorem tailTrace_5719182 : CollatzResearch.WordTrace tailWord_5719182 prefixEnd_5719182 2936689316542347907822967 := by
  unfold tailWord_5719182
  simp only [CollatzResearch.WordTrace]
  refine ⟨26074463045798480920873975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139063802910925231577994533 26074463045798480920873975)
  ·
    refine ⟨39111694568697721381310963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26074463045798480920873975 39111694568697721381310963)
    ·
      refine ⟨58667541853046582071966445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39111694568697721381310963 58667541853046582071966445)
      ·
        refine ⟨22000328194892468276987417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58667541853046582071966445 22000328194892468276987417)
        ·
          refine ⟨16500246146169351207740563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22000328194892468276987417 16500246146169351207740563)
          ·
            refine ⟨24750369219254026811610845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16500246146169351207740563 24750369219254026811610845)
            ·
              refine ⟨9281388457220260054354067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24750369219254026811610845 9281388457220260054354067)
              ·
                refine ⟨13922082685830390081531101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9281388457220260054354067 13922082685830390081531101)
                ·
                  refine ⟨5220781007186396280574163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13922082685830390081531101 5220781007186396280574163)
                  ·
                    refine ⟨7831171510779594420861245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220781007186396280574163 7831171510779594420861245)
                    ·
                      refine ⟨2936689316542347907822967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7831171510779594420861245 2936689316542347907822967)
                      ·
                        rfl

theorem cell23_5719182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5719182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719182 prefixEnd_5719182 := by exact prefixLift 5719182
  have htrace : WordTrace (prefixWord ++ tailWord_5719182) baseStart_5719182 baseEnd_5719182 := by
    simpa [prefixWord, tailWord_5719182, baseEnd_5719182] using wordTrace_append hprefix tailTrace_5719182
  have hstable : (prefixWord ++ tailWord_5719182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719182).length < 2 ^ (prefixWord ++ tailWord_5719182).sum := by decide
  have hdescent : baseEnd_5719182 < baseStart_5719182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719205 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_5719205 : Nat := 118140960795 + 5719205 * 2 ^ 59
def prefixEnd_5719205 : Nat := 4983230072969 + 3 ^ 40 * 5719205 * 2
def baseEnd_5719205 : Nat := 2936701126597401317835361

theorem tailTrace_5719205 : CollatzResearch.WordTrace tailWord_5719205 prefixEnd_5719205 2936701126597401317835361 := by
  unfold tailWord_5719205
  simp only [CollatzResearch.WordTrace]
  refine ⟨208596543245304522295079069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139064362163536348196719379 208596543245304522295079069)
  ·
    refine ⟨78223703716989195860654651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208596543245304522295079069 78223703716989195860654651)
    ·
      refine ⟨117335555575483793790981977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78223703716989195860654651 117335555575483793790981977)
      ·
        refine ⟨88001666681612845343236483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117335555575483793790981977 88001666681612845343236483)
        ·
          refine ⟨132002500022419268014854725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88001666681612845343236483 132002500022419268014854725)
          ·
            refine ⟨24750468754203612752785261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132002500022419268014854725 24750468754203612752785261)
            ·
              refine ⟨9281425782826354782294473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24750468754203612752785261 9281425782826354782294473)
              ·
                refine ⟨6961069337119766086720855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9281425782826354782294473 6961069337119766086720855)
                ·
                  refine ⟨10441604005679649130081283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961069337119766086720855 10441604005679649130081283)
                  ·
                    refine ⟨15662406008519473695121925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10441604005679649130081283 15662406008519473695121925)
                    ·
                      refine ⟨2936701126597401317835361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15662406008519473695121925 2936701126597401317835361)
                      ·
                        rfl

theorem cell23_5719205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_5719205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719205 prefixEnd_5719205 := by exact prefixLift 5719205
  have htrace : WordTrace (prefixWord ++ tailWord_5719205) baseStart_5719205 baseEnd_5719205 := by
    simpa [prefixWord, tailWord_5719205, baseEnd_5719205] using wordTrace_append hprefix tailTrace_5719205
  have hstable : (prefixWord ++ tailWord_5719205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719205).length < 2 ^ (prefixWord ++ tailWord_5719205).sum := by decide
  have hdescent : baseEnd_5719205 < baseStart_5719205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719218 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_5719218 : Nat := 118140960795 + 5719218 * 2 ^ 59
def prefixEnd_5719218 : Nat := 4983230072969 + 3 ^ 40 * 5719218 * 2
def baseEnd_5719218 : Nat := 2936707801845909766972801

theorem tailTrace_5719218 : CollatzResearch.WordTrace tailWord_5719218 prefixEnd_5719218 2936707801845909766972801 := by
  unfold tailWord_5719218
  simp only [CollatzResearch.WordTrace]
  refine ⟨52149254348564356378825577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139064678262838283676868205 52149254348564356378825577)
  ·
    refine ⟨39111940761423267284119183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52149254348564356378825577 39111940761423267284119183)
    ·
      refine ⟨58667911142134900926178775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39111940761423267284119183 58667911142134900926178775)
      ·
        refine ⟨88001866713202351389268163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58667911142134900926178775 88001866713202351389268163)
        ·
          refine ⟨132002800069803527083902245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88001866713202351389268163 132002800069803527083902245)
          ·
            refine ⟨24750525013088161328231671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132002800069803527083902245 24750525013088161328231671)
            ·
              refine ⟨37125787519632241992347507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24750525013088161328231671 37125787519632241992347507)
              ·
                refine ⟨55688681279448362988521261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37125787519632241992347507 55688681279448362988521261)
                ·
                  refine ⟨20883255479793136120695473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55688681279448362988521261 20883255479793136120695473)
                  ·
                    refine ⟨15662441609844852090521605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20883255479793136120695473 15662441609844852090521605)
                    ·
                      refine ⟨2936707801845909766972801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15662441609844852090521605 2936707801845909766972801)
                      ·
                        rfl

theorem cell23_5719218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_5719218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719218 prefixEnd_5719218 := by exact prefixLift 5719218
  have htrace : WordTrace (prefixWord ++ tailWord_5719218) baseStart_5719218 baseEnd_5719218 := by
    simpa [prefixWord, tailWord_5719218, baseEnd_5719218] using wordTrace_append hprefix tailTrace_5719218
  have hstable : (prefixWord ++ tailWord_5719218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719218).length < 2 ^ (prefixWord ++ tailWord_5719218).sum := by decide
  have hdescent : baseEnd_5719218 < baseStart_5719218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719225 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 5]
def baseStart_5719225 : Nat := 118140960795 + 5719225 * 2 ^ 59
def prefixEnd_5719225 : Nat := 4983230072969 + 3 ^ 40 * 5719225 * 2
def baseEnd_5719225 : Nat := 2936711396210491239585269

theorem tailTrace_5719225 : CollatzResearch.WordTrace tailWord_5719225 prefixEnd_5719225 2936711396210491239585269 := by
  unfold tailWord_5719225
  simp only [CollatzResearch.WordTrace]
  refine ⟨208597272705232065710807129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139064848470154710473871419 208597272705232065710807129)
  ·
    refine ⟨156447954528924049283105347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208597272705232065710807129 156447954528924049283105347)
    ·
      refine ⟨234671931793386073924658021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156447954528924049283105347 234671931793386073924658021)
      ·
        refine ⟨44000987211259888860873379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234671931793386073924658021 44000987211259888860873379)
        ·
          refine ⟨66001480816889833291310069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44000987211259888860873379 66001480816889833291310069)
          ·
            refine ⟨6187638826583421871060319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66001480816889833291310069 6187638826583421871060319)
            ·
              refine ⟨9281458239875132806590479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6187638826583421871060319 9281458239875132806590479)
              ·
                refine ⟨13922187359812699209885719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9281458239875132806590479 13922187359812699209885719)
                ·
                  refine ⟨20883281039719048814828579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13922187359812699209885719 20883281039719048814828579)
                  ·
                    refine ⟨31324921559578573222242869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20883281039719048814828579 31324921559578573222242869)
                    ·
                      refine ⟨2936711396210491239585269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31324921559578573222242869 2936711396210491239585269)
                      ·
                        rfl

theorem cell23_5719225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_5719225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719225 prefixEnd_5719225 := by exact prefixLift 5719225
  have htrace : WordTrace (prefixWord ++ tailWord_5719225) baseStart_5719225 baseEnd_5719225 := by
    simpa [prefixWord, tailWord_5719225, baseEnd_5719225] using wordTrace_append hprefix tailTrace_5719225
  have hstable : (prefixWord ++ tailWord_5719225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719225).length < 2 ^ (prefixWord ++ tailWord_5719225).sum := by decide
  have hdescent : baseEnd_5719225 < baseStart_5719225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719232 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 2, 4]
def baseStart_5719232 : Nat := 118140960795 + 5719232 * 2 ^ 59
def prefixEnd_5719232 : Nat := 4983230072969 + 3 ^ 40 * 5719232 * 2
def baseEnd_5719232 : Nat := 978904996858357570732579

theorem tailTrace_5719232 : CollatzResearch.WordTrace tailWord_5719232 prefixEnd_5719232 978904996858357570732579 := by
  unfold tailWord_5719232
  simp only [CollatzResearch.WordTrace]
  refine ⟨104298764008103352953155975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139065018677471137270874633 104298764008103352953155975)
  ·
    refine ⟨156448146012155029429733963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104298764008103352953155975 156448146012155029429733963)
    ·
      refine ⟨234672219018232544144600945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156448146012155029429733963 234672219018232544144600945)
      ·
        refine ⟨176004164263674408108450709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234672219018232544144600945 176004164263674408108450709)
        ·
          refine ⟨8250195199859737880083627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176004164263674408108450709 8250195199859737880083627)
          ·
            refine ⟨12375292799789606820125441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250195199859737880083627 12375292799789606820125441)
            ·
              refine ⟨9281469599842205115094081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12375292799789606820125441 9281469599842205115094081)
              ·
                refine ⟨6961102199881653836320561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9281469599842205115094081 6961102199881653836320561)
                ·
                  refine ⟨5220826649911240377240421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6961102199881653836320561 5220826649911240377240421)
                  ·
                    refine ⟨978904996858357570732579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5220826649911240377240421 978904996858357570732579)
                    ·
                      rfl

theorem cell23_5719232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_5719232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719232 prefixEnd_5719232 := by exact prefixLift 5719232
  have htrace : WordTrace (prefixWord ++ tailWord_5719232) baseStart_5719232 baseEnd_5719232 := by
    simpa [prefixWord, tailWord_5719232, baseEnd_5719232] using wordTrace_append hprefix tailTrace_5719232
  have hstable : (prefixWord ++ tailWord_5719232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719232).length < 2 ^ (prefixWord ++ tailWord_5719232).sum := by decide
  have hdescent : baseEnd_5719232 < baseStart_5719232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719233 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5719233 : Nat := 118140960795 + 5719233 * 2 ^ 59
def prefixEnd_5719233 : Nat := 4983230072969 + 3 ^ 40 * 5719233 * 2
def baseEnd_5719233 : Nat := 2936715504055727208285233

theorem tailTrace_5719233 : CollatzResearch.WordTrace tailWord_5719233 prefixEnd_5719233 2936715504055727208285233 := by
  unfold tailWord_5719233
  simp only [CollatzResearch.WordTrace]
  refine ⟨208597564489203083077098353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139065042992802055384732235 208597564489203083077098353)
  ·
    refine ⟨156448173366902312307823765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208597564489203083077098353 156448173366902312307823765)
    ·
      refine ⟨7333508126573545889429239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156448173366902312307823765 7333508126573545889429239)
      ·
        refine ⟨11000262189860318834143859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7333508126573545889429239 11000262189860318834143859)
        ·
          refine ⟨16500393284790478251215789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11000262189860318834143859 16500393284790478251215789)
          ·
            refine ⟨6187647481796429344205921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16500393284790478251215789 6187647481796429344205921)
            ·
              refine ⟨4640735611347322008154441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6187647481796429344205921 4640735611347322008154441)
              ·
                refine ⟨3480551708510491506115831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4640735611347322008154441 3480551708510491506115831)
                ·
                  refine ⟨5220827562765737259173747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480551708510491506115831 5220827562765737259173747)
                  ·
                    refine ⟨7831241344148605888760621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220827562765737259173747 7831241344148605888760621)
                    ·
                      refine ⟨2936715504055727208285233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7831241344148605888760621 2936715504055727208285233)
                      ·
                        rfl

theorem cell23_5719233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5719233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719233 prefixEnd_5719233 := by exact prefixLift 5719233
  have htrace : WordTrace (prefixWord ++ tailWord_5719233) baseStart_5719233 baseEnd_5719233 := by
    simpa [prefixWord, tailWord_5719233, baseEnd_5719233] using wordTrace_append hprefix tailTrace_5719233
  have hstable : (prefixWord ++ tailWord_5719233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719233).length < 2 ^ (prefixWord ++ tailWord_5719233).sum := by decide
  have hdescent : baseEnd_5719233 < baseStart_5719233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719385 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_5719385 : Nat := 118140960795 + 5719385 * 2 ^ 59
def prefixEnd_5719385 : Nat := 4983230072969 + 3 ^ 40 * 5719385 * 2
def baseEnd_5719385 : Nat := 2936793553115210613584533

theorem tailTrace_5719385 : CollatzResearch.WordTrace tailWord_5719385 prefixEnd_5719385 2936793553115210613584533 := by
  unfold tailWord_5719385
  simp only [CollatzResearch.WordTrace]
  refine ⟨208603108384652413036631609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139068738923101608691087739 208603108384652413036631609)
  ·
    refine ⟨156452331288489309777473707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208603108384652413036631609 156452331288489309777473707)
    ·
      refine ⟨234678496932733964666210561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156452331288489309777473707 234678496932733964666210561)
      ·
        refine ⟨176008872699550473499657921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234678496932733964666210561 176008872699550473499657921)
        ·
          refine ⟨132006654524662855124743441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176008872699550473499657921 132006654524662855124743441)
          ·
            refine ⟨99004990893497141343557581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132006654524662855124743441 99004990893497141343557581)
            ·
              refine ⟨37126871585061428003834093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99004990893497141343557581 37126871585061428003834093)
              ·
                refine ⟨13922576844398035501437785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37126871585061428003834093 13922576844398035501437785)
                ·
                  refine ⟨10441932633298526626078339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13922576844398035501437785 10441932633298526626078339)
                  ·
                    refine ⟨15662898949947789939117509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10441932633298526626078339 15662898949947789939117509)
                    ·
                      refine ⟨2936793553115210613584533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15662898949947789939117509 2936793553115210613584533)
                      ·
                        rfl

theorem cell23_5719385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_5719385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719385 prefixEnd_5719385 := by exact prefixLift 5719385
  have htrace : WordTrace (prefixWord ++ tailWord_5719385) baseStart_5719385 baseEnd_5719385 := by
    simpa [prefixWord, tailWord_5719385, baseEnd_5719385] using wordTrace_append hprefix tailTrace_5719385
  have hstable : (prefixWord ++ tailWord_5719385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719385).length < 2 ^ (prefixWord ++ tailWord_5719385).sum := by decide
  have hdescent : baseEnd_5719385 < baseStart_5719385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719475 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 4]
def baseStart_5719475 : Nat := 118140960795 + 5719475 * 2 ^ 59
def prefixEnd_5719475 : Nat := 4983230072969 + 3 ^ 40 * 5719475 * 2
def baseEnd_5719475 : Nat := 2936839766374115261459119

theorem tailTrace_5719475 : CollatzResearch.WordTrace tailWord_5719475 prefixEnd_5719475 2936839766374115261459119 := by
  unfold tailWord_5719475
  simp only [CollatzResearch.WordTrace]
  refine ⟨208606390954326358407407879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139070927302884238938271919 208606390954326358407407879)
  ·
    refine ⟨312909586431489537611111819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208606390954326358407407879 312909586431489537611111819)
    ·
      refine ⟨469364379647234306416667729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312909586431489537611111819 469364379647234306416667729)
      ·
        refine ⟨352023284735425729812500797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469364379647234306416667729 352023284735425729812500797)
        ·
          refine ⟨132008731775784648679687799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352023284735425729812500797 132008731775784648679687799)
          ·
            refine ⟨198013097663676973019531699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132008731775784648679687799 198013097663676973019531699)
            ·
              refine ⟨297019646495515459529297549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198013097663676973019531699 297019646495515459529297549)
              ·
                refine ⟨111382367435818297323486581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297019646495515459529297549 111382367435818297323486581)
                ·
                  refine ⟨10442096947107965374076867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111382367435818297323486581 10442096947107965374076867)
                  ·
                    refine ⟨15663145420661948061115301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10442096947107965374076867 15663145420661948061115301)
                    ·
                      refine ⟨2936839766374115261459119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15663145420661948061115301 2936839766374115261459119)
                      ·
                        rfl

theorem cell23_5719475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_5719475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719475 prefixEnd_5719475 := by exact prefixLift 5719475
  have htrace : WordTrace (prefixWord ++ tailWord_5719475) baseStart_5719475 baseEnd_5719475 := by
    simpa [prefixWord, tailWord_5719475, baseEnd_5719475] using wordTrace_append hprefix tailTrace_5719475
  have hstable : (prefixWord ++ tailWord_5719475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719475).length < 2 ^ (prefixWord ++ tailWord_5719475).sum := by decide
  have hdescent : baseEnd_5719475 < baseStart_5719475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719495 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_5719495 : Nat := 118140960795 + 5719495 * 2 ^ 59
def prefixEnd_5719495 : Nat := 4983230072969 + 3 ^ 40 * 5719495 * 2
def baseEnd_5719495 : Nat := 2936850035987205183209027

theorem tailTrace_5719495 : CollatzResearch.WordTrace tailWord_5719495 prefixEnd_5719495 2936850035987205183209027 := by
  unfold tailWord_5719495
  simp only [CollatzResearch.WordTrace]
  refine ⟨208607120414253901823135939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139071413609502601215423959 208607120414253901823135939)
  ·
    refine ⟨312910680621380852734703909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208607120414253901823135939 312910680621380852734703909)
    ·
      refine ⟨58670752616508909887756983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312910680621380852734703909 58670752616508909887756983)
      ·
        refine ⟨88006128924763364831635475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58670752616508909887756983 88006128924763364831635475)
        ·
          refine ⟨132009193387145047247453213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88006128924763364831635475 132009193387145047247453213)
          ·
            refine ⟨49503447520179392717794955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132009193387145047247453213 49503447520179392717794955)
            ·
              refine ⟨74255171280269089076692433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49503447520179392717794955 74255171280269089076692433)
              ·
                refine ⟨55691378460201816807519325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74255171280269089076692433 55691378460201816807519325)
                ·
                  refine ⟨20884266922575681302819747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55691378460201816807519325 20884266922575681302819747)
                  ·
                    refine ⟨31326400383863521954229621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20884266922575681302819747 31326400383863521954229621)
                    ·
                      refine ⟨2936850035987205183209027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31326400383863521954229621 2936850035987205183209027)
                      ·
                        rfl

theorem cell23_5719495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_5719495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719495 prefixEnd_5719495 := by exact prefixLift 5719495
  have htrace : WordTrace (prefixWord ++ tailWord_5719495) baseStart_5719495 baseEnd_5719495 := by
    simpa [prefixWord, tailWord_5719495, baseEnd_5719495] using wordTrace_append hprefix tailTrace_5719495
  have hstable : (prefixWord ++ tailWord_5719495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719495).length < 2 ^ (prefixWord ++ tailWord_5719495).sum := by decide
  have hdescent : baseEnd_5719495 < baseStart_5719495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719502 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_5719502 : Nat := 118140960795 + 5719502 * 2 ^ 59
def prefixEnd_5719502 : Nat := 4983230072969 + 3 ^ 40 * 5719502 * 2
def baseEnd_5719502 : Nat := 978951210117262218607165

theorem tailTrace_5719502 : CollatzResearch.WordTrace tailWord_5719502 prefixEnd_5719502 978951210117262218607165 := by
  unfold tailWord_5719502
  simp only [CollatzResearch.WordTrace]
  refine ⟨26075921965653567752330095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139071583816819028012427173 26075921965653567752330095)
  ·
    refine ⟨39113882948480351628495143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26075921965653567752330095 39113882948480351628495143)
    ·
      refine ⟨58670824422720527442742715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39113882948480351628495143 58670824422720527442742715)
      ·
        refine ⟨88006236634080791164114073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58670824422720527442742715 88006236634080791164114073)
        ·
          refine ⟨66004677475560593373085555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88006236634080791164114073 66004677475560593373085555)
          ·
            refine ⟨99007016213340890059628333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66004677475560593373085555 99007016213340890059628333)
            ·
              refine ⟨37127631080002833772360625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99007016213340890059628333 37127631080002833772360625)
              ·
                refine ⟨27845723310002125329270469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37127631080002833772360625 27845723310002125329270469)
                ·
                  refine ⟨5221073120625398499238213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27845723310002125329270469 5221073120625398499238213)
                  ·
                    refine ⟨978951210117262218607165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5221073120625398499238213 978951210117262218607165)
                    ·
                      rfl

theorem cell23_5719502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_5719502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719502 prefixEnd_5719502 := by exact prefixLift 5719502
  have htrace : WordTrace (prefixWord ++ tailWord_5719502) baseStart_5719502 baseEnd_5719502 := by
    simpa [prefixWord, tailWord_5719502, baseEnd_5719502] using wordTrace_append hprefix tailTrace_5719502
  have hstable : (prefixWord ++ tailWord_5719502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719502).length < 2 ^ (prefixWord ++ tailWord_5719502).sum := by decide
  have hdescent : baseEnd_5719502 < baseStart_5719502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719536 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 2, 4]
def baseStart_5719536 : Nat := 118140960795 + 5719536 * 2 ^ 59
def prefixEnd_5719536 : Nat := 4983230072969 + 3 ^ 40 * 5719536 * 2
def baseEnd_5719536 : Nat := 978957029564679840932113

theorem tailTrace_5719536 : CollatzResearch.WordTrace tailWord_5719536 prefixEnd_5719536 978957029564679840932113 := by
  unfold tailWord_5719536
  simp only [CollatzResearch.WordTrace]
  refine ⟨104304307903552682912689231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139072410538070243883585641 104304307903552682912689231)
  ·
    refine ⟨156456461855329024369033847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104304307903552682912689231 156456461855329024369033847)
    ·
      refine ⟨234684692782993536553550771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156456461855329024369033847 234684692782993536553550771)
      ·
        refine ⟨352027039174490304830326157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234684692782993536553550771 352027039174490304830326157)
        ·
          refine ⟨132010139690433864311372309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352027039174490304830326157 132010139690433864311372309)
          ·
            refine ⟨6187975297989087389595577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132010139690433864311372309 6187975297989087389595577)
            ·
              refine ⟨4640981473491815542196683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6187975297989087389595577 4640981473491815542196683)
              ·
                refine ⟨6961472210237723313295025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4640981473491815542196683 6961472210237723313295025)
                ·
                  refine ⟨5221104157678292484971269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6961472210237723313295025 5221104157678292484971269)
                  ·
                    refine ⟨978957029564679840932113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5221104157678292484971269 978957029564679840932113)
                    ·
                      rfl

theorem cell23_5719536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 4].length) (baseStart_5719536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719536 prefixEnd_5719536 := by exact prefixLift 5719536
  have htrace : WordTrace (prefixWord ++ tailWord_5719536) baseStart_5719536 baseEnd_5719536 := by
    simpa [prefixWord, tailWord_5719536, baseEnd_5719536] using wordTrace_append hprefix tailTrace_5719536
  have hstable : (prefixWord ++ tailWord_5719536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719536).length < 2 ^ (prefixWord ++ tailWord_5719536).sum := by decide
  have hdescent : baseEnd_5719536 < baseStart_5719536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719555 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_5719555 : Nat := 118140960795 + 5719555 * 2 ^ 59
def prefixEnd_5719555 : Nat := 4983230072969 + 3 ^ 40 * 5719555 * 2
def baseEnd_5719555 : Nat := 2936880844826474948458751

theorem tailTrace_5719555 : CollatzResearch.WordTrace tailWord_5719555 prefixEnd_5719555 2936880844826474948458751 := by
  unfold tailWord_5719555
  simp only [CollatzResearch.WordTrace]
  refine ⟨208609308794036532070320119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139072872529357688046880079 208609308794036532070320119)
  ·
    refine ⟨312913963191054798105480179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208609308794036532070320119 312913963191054798105480179)
    ·
      refine ⟨469370944786582197158220269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312913963191054798105480179 469370944786582197158220269)
      ·
        refine ⟨176014104294968323934332601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469370944786582197158220269 176014104294968323934332601)
        ·
          refine ⟨132010578221226242950749451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176014104294968323934332601 132010578221226242950749451)
          ·
            refine ⟨198015867331839364426124177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132010578221226242950749451 198015867331839364426124177)
            ·
              refine ⟨148511900498879523319593133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198015867331839364426124177 148511900498879523319593133)
              ·
                refine ⟨55691962687079821244847425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148511900498879523319593133 55691962687079821244847425)
                ·
                  refine ⟨41768972015309865933635569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55691962687079821244847425 41768972015309865933635569)
                  ·
                    refine ⟨31326729011482399450226677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41768972015309865933635569 31326729011482399450226677)
                    ·
                      refine ⟨2936880844826474948458751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31326729011482399450226677 2936880844826474948458751)
                      ·
                        rfl

theorem cell23_5719555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_5719555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719555 prefixEnd_5719555 := by exact prefixLift 5719555
  have htrace : WordTrace (prefixWord ++ tailWord_5719555) baseStart_5719555 baseEnd_5719555 := by
    simpa [prefixWord, tailWord_5719555, baseEnd_5719555] using wordTrace_append hprefix tailTrace_5719555
  have hstable : (prefixWord ++ tailWord_5719555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719555).length < 2 ^ (prefixWord ++ tailWord_5719555).sum := by decide
  have hdescent : baseEnd_5719555 < baseStart_5719555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719559 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5719559 : Nat := 118140960795 + 5719559 * 2 ^ 59
def prefixEnd_5719559 : Nat := 4983230072969 + 3 ^ 40 * 5719559 * 2
def baseEnd_5719559 : Nat := 2936882898749092932808733

theorem tailTrace_5719559 : CollatzResearch.WordTrace tailWord_5719559 prefixEnd_5719559 2936882898749092932808733 := by
  unfold tailWord_5719559
  simp only [CollatzResearch.WordTrace]
  refine ⟨208609454686022040753465731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139072969790681360502310487 208609454686022040753465731)
  ·
    refine ⟨312914182029033061130198597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208609454686022040753465731 312914182029033061130198597)
    ·
      refine ⟨58671409130443698961912237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312914182029033061130198597 58671409130443698961912237)
      ·
        refine ⟨22001778423916387110717089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58671409130443698961912237 22001778423916387110717089)
        ·
          refine ⟨16501333817937290333037817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22001778423916387110717089 16501333817937290333037817)
          ·
            refine ⟨12376000363452967749778363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16501333817937290333037817 12376000363452967749778363)
            ·
              refine ⟨18564000545179451624667545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12376000363452967749778363 18564000545179451624667545)
              ·
                refine ⟨13923000408884588718500659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18564000545179451624667545 13923000408884588718500659)
                ·
                  refine ⟨20884500613326883077750989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13923000408884588718500659 20884500613326883077750989)
                  ·
                    refine ⟨7831687729997581154156621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20884500613326883077750989 7831687729997581154156621)
                    ·
                      refine ⟨2936882898749092932808733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7831687729997581154156621 2936882898749092932808733)
                      ·
                        rfl

theorem cell23_5719559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5719559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719559 prefixEnd_5719559 := by exact prefixLift 5719559
  have htrace : WordTrace (prefixWord ++ tailWord_5719559) baseStart_5719559 baseEnd_5719559 := by
    simpa [prefixWord, tailWord_5719559, baseEnd_5719559] using wordTrace_append hprefix tailTrace_5719559
  have hstable : (prefixWord ++ tailWord_5719559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719559).length < 2 ^ (prefixWord ++ tailWord_5719559).sum := by decide
  have hdescent : baseEnd_5719559 < baseStart_5719559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719602 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_5719602 : Nat := 118140960795 + 5719602 * 2 ^ 59
def prefixEnd_5719602 : Nat := 4983230072969 + 3 ^ 40 * 5719602 * 2
def baseEnd_5719602 : Nat := 2936904978417236264571035

theorem tailTrace_5719602 : CollatzResearch.WordTrace tailWord_5719602 prefixEnd_5719602 2936904978417236264571035 := by
  unfold tailWord_5719602
  simp only [CollatzResearch.WordTrace]
  refine ⟨52152755756216564774320265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139074015349910839398187373 52152755756216564774320265)
  ·
    refine ⟨39114566817162423580740199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52152755756216564774320265 39114566817162423580740199)
    ·
      refine ⟨58671850225743635371110299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39114566817162423580740199 58671850225743635371110299)
      ·
        refine ⟨88007775338615453056665449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58671850225743635371110299 88007775338615453056665449)
        ·
          refine ⟨66005831503961589792499087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88007775338615453056665449 66005831503961589792499087)
          ·
            refine ⟨99008747255942384688748631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66005831503961589792499087 99008747255942384688748631)
            ·
              refine ⟨148513120883913577033122947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99008747255942384688748631 148513120883913577033122947)
              ·
                refine ⟨222769681325870365549684421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148513120883913577033122947 222769681325870365549684421)
                ·
                  refine ⟨41769315248600693540565829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222769681325870365549684421 41769315248600693540565829)
                  ·
                    refine ⟨7831746609112630038856093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41769315248600693540565829 7831746609112630038856093)
                    ·
                      refine ⟨2936904978417236264571035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7831746609112630038856093 2936904978417236264571035)
                      ·
                        rfl

theorem cell23_5719602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_5719602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719602 prefixEnd_5719602 := by exact prefixLift 5719602
  have htrace : WordTrace (prefixWord ++ tailWord_5719602) baseStart_5719602 baseEnd_5719602 := by
    simpa [prefixWord, tailWord_5719602, baseEnd_5719602] using wordTrace_append hprefix tailTrace_5719602
  have hstable : (prefixWord ++ tailWord_5719602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719602).length < 2 ^ (prefixWord ++ tailWord_5719602).sum := by decide
  have hdescent : baseEnd_5719602 < baseStart_5719602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719632 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_5719632 : Nat := 118140960795 + 5719632 * 2 ^ 59
def prefixEnd_5719632 : Nat := 4983230072969 + 3 ^ 40 * 5719632 * 2
def baseEnd_5719632 : Nat := 2936920382836871147195897

theorem tailTrace_5719632 : CollatzResearch.WordTrace tailWord_5719632 prefixEnd_5719632 2936920382836871147195897 := by
  unfold tailWord_5719632
  simp only [CollatzResearch.WordTrace]
  refine ⟨104306058607378787110436575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139074744809838382813915433 104306058607378787110436575)
  ·
    refine ⟨156459087911068180665654863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104306058607378787110436575 156459087911068180665654863)
    ·
      refine ⟨234688631866602270998482295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156459087911068180665654863 234688631866602270998482295)
      ·
        refine ⟨352032947799903406497723443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234688631866602270998482295 352032947799903406497723443)
        ·
          refine ⟨528049421699855109746585165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352032947799903406497723443 528049421699855109746585165)
          ·
            refine ⟨198018533137445666154969437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528049421699855109746585165 198018533137445666154969437)
            ·
              refine ⟨74256949926542124808113539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198018533137445666154969437 74256949926542124808113539)
              ·
                refine ⟨111385424889813187212170309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74256949926542124808113539 111385424889813187212170309)
                ·
                  refine ⟨20884767166839972602281933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111385424889813187212170309 20884767166839972602281933)
                  ·
                    refine ⟨7831787687564989725855725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20884767166839972602281933 7831787687564989725855725)
                    ·
                      refine ⟨2936920382836871147195897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7831787687564989725855725 2936920382836871147195897)
                      ·
                        rfl

theorem cell23_5719632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_5719632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719632 prefixEnd_5719632 := by exact prefixLift 5719632
  have htrace : WordTrace (prefixWord ++ tailWord_5719632) baseStart_5719632 baseEnd_5719632 := by
    simpa [prefixWord, tailWord_5719632, baseEnd_5719632] using wordTrace_append hprefix tailTrace_5719632
  have hstable : (prefixWord ++ tailWord_5719632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719632).length < 2 ^ (prefixWord ++ tailWord_5719632).sum := by decide
  have hdescent : baseEnd_5719632 < baseStart_5719632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719635 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 11]
def baseStart_5719635 : Nat := 118140960795 + 5719635 * 2 ^ 59
def prefixEnd_5719635 : Nat := 4983230072969 + 3 ^ 40 * 5719635 * 2
def baseEnd_5719635 : Nat := 978973974426278211819461

theorem tailTrace_5719635 : CollatzResearch.WordTrace tailWord_5719635 prefixEnd_5719635 978973974426278211819461 := by
  unfold tailWord_5719635
  simp only [CollatzResearch.WordTrace]
  refine ⟨208612226633746705733232359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139074817755831137155488239 208612226633746705733232359)
  ·
    refine ⟨312918339950620058599848539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208612226633746705733232359 312918339950620058599848539)
    ·
      refine ⟨469377509925930087899772809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312918339950620058599848539 469377509925930087899772809)
      ·
        refine ⟨352033132444447565924829607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469377509925930087899772809 352033132444447565924829607)
        ·
          refine ⟨528049698666671348887244411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352033132444447565924829607 528049698666671348887244411)
          ·
            refine ⟨792074548000007023330866617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528049698666671348887244411 792074548000007023330866617)
            ·
              refine ⟨594055911000005267498149963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792074548000007023330866617 594055911000005267498149963)
              ·
                refine ⟨891083866500007901247224945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594055911000005267498149963 891083866500007901247224945)
                ·
                  refine ⟨668312899875005925935418709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 891083866500007901247224945 668312899875005925935418709)
                  ·
                    refine ⟨978973974426278211819461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 668312899875005925935418709 978973974426278211819461)
                    ·
                      rfl

theorem cell23_5719635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_5719635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719635 prefixEnd_5719635 := by exact prefixLift 5719635
  have htrace : WordTrace (prefixWord ++ tailWord_5719635) baseStart_5719635 baseEnd_5719635 := by
    simpa [prefixWord, tailWord_5719635, baseEnd_5719635] using wordTrace_append hprefix tailTrace_5719635
  have hstable : (prefixWord ++ tailWord_5719635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719635).length < 2 ^ (prefixWord ++ tailWord_5719635).sum := by decide
  have hdescent : baseEnd_5719635 < baseStart_5719635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719639 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 5]
def baseStart_5719639 : Nat := 118140960795 + 5719639 * 2 ^ 59
def prefixEnd_5719639 : Nat := 4983230072969 + 3 ^ 40 * 5719639 * 2
def baseEnd_5719639 : Nat := 326324886355716957756485

theorem tailTrace_5719639 : CollatzResearch.WordTrace tailWord_5719639 prefixEnd_5719639 326324886355716957756485 := by
  unfold tailWord_5719639
  simp only [CollatzResearch.WordTrace]
  refine ⟨208612372525732214416377971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139074915017154809610918647 208612372525732214416377971)
  ·
    refine ⟨312918558788598321624566957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208612372525732214416377971 312918558788598321624566957)
    ·
      refine ⟨117344459545724370609212609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312918558788598321624566957 117344459545724370609212609)
      ·
        refine ⟨88008344659293277956909457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117344459545724370609212609 88008344659293277956909457)
        ·
          refine ⟨66006258494469958467682093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88008344659293277956909457 66006258494469958467682093)
          ·
            refine ⟨24752346935426234425380785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66006258494469958467682093 24752346935426234425380785)
            ·
              refine ⟨18564260201569675819035589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24752346935426234425380785 18564260201569675819035589)
              ·
                refine ⟨3480798787794314216069173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18564260201569675819035589 3480798787794314216069173)
                ·
                  refine ⟨326324886355716957756485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480798787794314216069173 326324886355716957756485)
                  ·
                    rfl

theorem cell23_5719639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 5].length) (baseStart_5719639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719639 prefixEnd_5719639 := by exact prefixLift 5719639
  have htrace : WordTrace (prefixWord ++ tailWord_5719639) baseStart_5719639 baseEnd_5719639 := by
    simpa [prefixWord, tailWord_5719639, baseEnd_5719639] using wordTrace_append hprefix tailTrace_5719639
  have hstable : (prefixWord ++ tailWord_5719639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719639).length < 2 ^ (prefixWord ++ tailWord_5719639).sum := by decide
  have hdescent : baseEnd_5719639 < baseStart_5719639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719652 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_5719652 : Nat := 118140960795 + 5719652 * 2 ^ 59
def prefixEnd_5719652 : Nat := 4983230072969 + 3 ^ 40 * 5719652 * 2
def baseEnd_5719652 : Nat := 978976884149987022981935

theorem tailTrace_5719652 : CollatzResearch.WordTrace tailWord_5719652 prefixEnd_5719652 978976884149987022981935 := by
  unfold tailWord_5719652
  simp only [CollatzResearch.WordTrace]
  refine ⟨104306423337342558818300605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139075231116456745091067473 104306423337342558818300605)
  ·
    refine ⟨39114908751503459556862727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104306423337342558818300605 39114908751503459556862727)
    ·
      refine ⟨58672363127255189335294091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39114908751503459556862727 58672363127255189335294091)
      ·
        refine ⟨88008544690882784002941137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58672363127255189335294091 88008544690882784002941137)
        ·
          refine ⟨66006408518162088002205853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88008544690882784002941137 66006408518162088002205853)
          ·
            refine ⟨24752403194310783000827195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66006408518162088002205853 24752403194310783000827195)
            ·
              refine ⟨37128604791466174501240793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24752403194310783000827195 37128604791466174501240793)
              ·
                refine ⟨27846453593599630875930595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37128604791466174501240793 27846453593599630875930595)
                ·
                  refine ⟨41769680390399446313895893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27846453593599630875930595 41769680390399446313895893)
                  ·
                    refine ⟨978976884149987022981935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41769680390399446313895893 978976884149987022981935)
                    ·
                      rfl

theorem cell23_5719652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_5719652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719652 prefixEnd_5719652 := by exact prefixLift 5719652
  have htrace : WordTrace (prefixWord ++ tailWord_5719652) baseStart_5719652 baseEnd_5719652 := by
    simpa [prefixWord, tailWord_5719652, baseEnd_5719652] using wordTrace_append hprefix tailTrace_5719652
  have hstable : (prefixWord ++ tailWord_5719652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719652).length < 2 ^ (prefixWord ++ tailWord_5719652).sum := by decide
  have hdescent : baseEnd_5719652 < baseStart_5719652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719669 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5719669 : Nat := 118140960795 + 5719669 * 2 ^ 59
def prefixEnd_5719669 : Nat := 4983230072969 + 3 ^ 40 * 5719669 * 2
def baseEnd_5719669 : Nat := 978979793873695834144409

theorem tailTrace_5719669 : CollatzResearch.WordTrace tailWord_5719669 prefixEnd_5719669 978979793873695834144409 := by
  unfold tailWord_5719669
  simp only [CollatzResearch.WordTrace]
  refine ⟨208613466715623529539970061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139075644477082353026646707 208613466715623529539970061)
  ·
    refine ⟨78230050018358823577488773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208613466715623529539970061 78230050018358823577488773)
    ·
      refine ⟨14668134378442279420779145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78230050018358823577488773 14668134378442279420779145)
      ·
        refine ⟨11001100783831709565584359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14668134378442279420779145 11001100783831709565584359)
        ·
          refine ⟨16501651175747564348376539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11001100783831709565584359 16501651175747564348376539)
          ·
            refine ⟨24752476763621346522564809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16501651175747564348376539 24752476763621346522564809)
            ·
              refine ⟨18564357572716009891923607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24752476763621346522564809 18564357572716009891923607)
              ·
                refine ⟨27846536359074014837885411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18564357572716009891923607 27846536359074014837885411)
                ·
                  refine ⟨41769804538611022256828117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27846536359074014837885411 41769804538611022256828117)
                  ·
                    refine ⟨978979793873695834144409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41769804538611022256828117 978979793873695834144409)
                    ·
                      rfl

theorem cell23_5719669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5719669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719669 prefixEnd_5719669 := by exact prefixLift 5719669
  have htrace : WordTrace (prefixWord ++ tailWord_5719669) baseStart_5719669 baseEnd_5719669 := by
    simpa [prefixWord, tailWord_5719669, baseEnd_5719669] using wordTrace_append hprefix tailTrace_5719669
  have hstable : (prefixWord ++ tailWord_5719669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719669).length < 2 ^ (prefixWord ++ tailWord_5719669).sum := by decide
  have hdescent : baseEnd_5719669 < baseStart_5719669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719689 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 4, 4, 2]
def baseStart_5719689 : Nat := 118140960795 + 5719689 * 2 ^ 59
def prefixEnd_5719689 : Nat := 4983230072969 + 3 ^ 40 * 5719689 * 2
def baseEnd_5719689 : Nat := 2936949651234177424183135

theorem tailTrace_5719689 : CollatzResearch.WordTrace tailWord_5719689 prefixEnd_5719689 2936949651234177424183135 := by
  unfold tailWord_5719689
  simp only [CollatzResearch.WordTrace]
  refine ⟨208614196175551072955698121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139076130783700715303798747 208614196175551072955698121)
  ·
    refine ⟨156460647131663304716773591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208614196175551072955698121 156460647131663304716773591)
    ·
      refine ⟨234690970697494957075160387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156460647131663304716773591 234690970697494957075160387)
      ·
        refine ⟨352036456046242435612740581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234690970697494957075160387 352036456046242435612740581)
        ·
          refine ⟨66006835508670456677388859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352036456046242435612740581 66006835508670456677388859)
          ·
            refine ⟨99010253263005685016083289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66006835508670456677388859 99010253263005685016083289)
            ·
              refine ⟨74257689947254263762062467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99010253263005685016083289 74257689947254263762062467)
              ·
                refine ⟨111386534920881395643093701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74257689947254263762062467 111386534920881395643093701)
                ·
                  refine ⟨20884975297665261683080069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111386534920881395643093701 20884975297665261683080069)
                  ·
                    refine ⟨3915932868312236565577513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20884975297665261683080069 3915932868312236565577513)
                    ·
                      refine ⟨2936949651234177424183135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3915932868312236565577513 2936949651234177424183135)
                      ·
                        rfl

theorem cell23_5719689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 4, 2].length) (baseStart_5719689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719689 prefixEnd_5719689 := by exact prefixLift 5719689
  have htrace : WordTrace (prefixWord ++ tailWord_5719689) baseStart_5719689 baseEnd_5719689 := by
    simpa [prefixWord, tailWord_5719689, baseEnd_5719689] using wordTrace_append hprefix tailTrace_5719689
  have hstable : (prefixWord ++ tailWord_5719689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719689).length < 2 ^ (prefixWord ++ tailWord_5719689).sum := by decide
  have hdescent : baseEnd_5719689 < baseStart_5719689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719709 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_5719709 : Nat := 118140960795 + 5719709 * 2 ^ 59
def prefixEnd_5719709 : Nat := 4983230072969 + 3 ^ 40 * 5719709 * 2
def baseEnd_5719709 : Nat := 2936959920847267345933043

theorem tailTrace_5719709 : CollatzResearch.WordTrace tailWord_5719709 prefixEnd_5719709 2936959920847267345933043 := by
  unfold tailWord_5719709
  simp only [CollatzResearch.WordTrace]
  refine ⟨208614925635478616371426181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139076617090319077580950787 208614925635478616371426181)
  ·
    refine ⟨39115298556652240569642409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208614925635478616371426181 39115298556652240569642409)
    ·
      refine ⟨29336473917489180427231807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39115298556652240569642409 29336473917489180427231807)
      ·
        refine ⟨44004710876233770640847711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29336473917489180427231807 44004710876233770640847711)
        ·
          refine ⟨66007066314350655961271567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44004710876233770640847711 66007066314350655961271567)
          ·
            refine ⟨99010599471525983941907351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66007066314350655961271567 99010599471525983941907351)
            ·
              refine ⟨148515899207288975912861027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99010599471525983941907351 148515899207288975912861027)
              ·
                refine ⟨222773848810933463869291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148515899207288975912861027 222773848810933463869291541)
                ·
                  refine ⟨10442524163012506118873041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222773848810933463869291541 10442524163012506118873041)
                  ·
                    refine ⟨7831893122259379589154781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10442524163012506118873041 7831893122259379589154781)
                    ·
                      refine ⟨2936959920847267345933043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7831893122259379589154781 2936959920847267345933043)
                      ·
                        rfl

theorem cell23_5719709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_5719709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719709 prefixEnd_5719709 := by exact prefixLift 5719709
  have htrace : WordTrace (prefixWord ++ tailWord_5719709) baseStart_5719709 baseEnd_5719709 := by
    simpa [prefixWord, tailWord_5719709, baseEnd_5719709] using wordTrace_append hprefix tailTrace_5719709
  have hstable : (prefixWord ++ tailWord_5719709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719709).length < 2 ^ (prefixWord ++ tailWord_5719709).sum := by decide
  have hdescent : baseEnd_5719709 < baseStart_5719709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719720 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5719720 : Nat := 118140960795 + 5719720 * 2 ^ 59
def prefixEnd_5719720 : Nat := 4983230072969 + 3 ^ 40 * 5719720 * 2
def baseEnd_5719720 : Nat := 978988523044822267631831

theorem tailTrace_5719720 : CollatzResearch.WordTrace tailWord_5719720 prefixEnd_5719720 978988523044822267631831 := by
  unfold tailWord_5719720
  simp only [CollatzResearch.WordTrace]
  refine ⟨104307663419219382625038307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139076884558959176833384409 104307663419219382625038307)
  ·
    refine ⟨156461495128829073937557461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104307663419219382625038307 156461495128829073937557461)
    ·
      refine ⟨3667066292081931420411503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 156461495128829073937557461 3667066292081931420411503)
      ·
        refine ⟨5500599438122897130617255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667066292081931420411503 5500599438122897130617255)
        ·
          refine ⟨8250899157184345695925883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500599438122897130617255 8250899157184345695925883)
          ·
            refine ⟨12376348735776518543888825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250899157184345695925883 12376348735776518543888825)
            ·
              refine ⟨9282261551832388907916619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12376348735776518543888825 9282261551832388907916619)
              ·
                refine ⟨13923392327748583361874929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9282261551832388907916619 13923392327748583361874929)
                ·
                  refine ⟨10442544245811437521406197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13923392327748583361874929 10442544245811437521406197)
                  ·
                    refine ⟨978988523044822267631831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10442544245811437521406197 978988523044822267631831)
                    ·
                      rfl

theorem cell23_5719720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5719720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719720 prefixEnd_5719720 := by exact prefixLift 5719720
  have htrace : WordTrace (prefixWord ++ tailWord_5719720) baseStart_5719720 baseEnd_5719720 := by
    simpa [prefixWord, tailWord_5719720, baseEnd_5719720] using wordTrace_append hprefix tailTrace_5719720
  have hstable : (prefixWord ++ tailWord_5719720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719720).length < 2 ^ (prefixWord ++ tailWord_5719720).sum := by decide
  have hdescent : baseEnd_5719720 < baseStart_5719720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719790 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_5719790 : Nat := 118140960795 + 5719790 * 2 ^ 59
def prefixEnd_5719790 : Nat := 4983230072969 + 3 ^ 40 * 5719790 * 2
def baseEnd_5719790 : Nat := 2937001512780281529020171

theorem tailTrace_5719790 : CollatzResearch.WordTrace tailWord_5719790 prefixEnd_5719790 2937001512780281529020171 := by
  unfold tailWord_5719790
  simp only [CollatzResearch.WordTrace]
  refine ⟨26077234993523145900640603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139078586632123444803416549 26077234993523145900640603)
  ·
    refine ⟨39115852490284718850960905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26077234993523145900640603 39115852490284718850960905)
    ·
      refine ⟨29336889367713539138220679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39115852490284718850960905 29336889367713539138220679)
      ·
        refine ⟨44005334051570308707331019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29336889367713539138220679 44005334051570308707331019)
        ·
          refine ⟨66008001077355463060996529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44005334051570308707331019 66008001077355463060996529)
          ·
            refine ⟨49506000808016597295747397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66008001077355463060996529 49506000808016597295747397)
            ·
              refine ⟨9282375151503111992952637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49506000808016597295747397 9282375151503111992952637)
              ·
                refine ⟨3480890681813666997357239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9282375151503111992952637 3480890681813666997357239)
                ·
                  refine ⟨5221336022720500496035859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480890681813666997357239 5221336022720500496035859)
                  ·
                    refine ⟨7832004034080750744053789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5221336022720500496035859 7832004034080750744053789)
                    ·
                      refine ⟨2937001512780281529020171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832004034080750744053789 2937001512780281529020171)
                      ·
                        rfl

theorem cell23_5719790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_5719790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719790 prefixEnd_5719790 := by exact prefixLift 5719790
  have htrace : WordTrace (prefixWord ++ tailWord_5719790) baseStart_5719790 baseEnd_5719790 := by
    simpa [prefixWord, tailWord_5719790, baseEnd_5719790] using wordTrace_append hprefix tailTrace_5719790
  have hstable : (prefixWord ++ tailWord_5719790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719790).length < 2 ^ (prefixWord ++ tailWord_5719790).sum := by decide
  have hdescent : baseEnd_5719790 < baseStart_5719790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719793 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 1, 5]
def baseStart_5719793 : Nat := 118140960795 + 5719793 * 2 ^ 59
def prefixEnd_5719793 : Nat := 4983230072969 + 3 ^ 40 * 5719793 * 2
def baseEnd_5719793 : Nat := 979001017740748339094219

theorem tailTrace_5719793 : CollatzResearch.WordTrace tailWord_5719793 prefixEnd_5719793 979001017740748339094219 := by
  unfold tailWord_5719793
  simp only [CollatzResearch.WordTrace]
  refine ⟨208617989367174298717484033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139078659578116199144989355 208617989367174298717484033)
  ·
    refine ⟨156463492025380724038113025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208617989367174298717484033 156463492025380724038113025)
    ·
      refine ⟨117347619019035543028584769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156463492025380724038113025 117347619019035543028584769)
      ·
        refine ⟨88010714264276657271438577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117347619019035543028584769 88010714264276657271438577)
        ·
          refine ⟨66008035698207492953578933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88010714264276657271438577 66008035698207492953578933)
          ·
            refine ⟨6188253346706952464398025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66008035698207492953578933 6188253346706952464398025)
            ·
              refine ⟨4641190010030214348298519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188253346706952464398025 4641190010030214348298519)
              ·
                refine ⟨6961785015045321522447779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641190010030214348298519 6961785015045321522447779)
                ·
                  refine ⟨10442677522567982283671669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961785015045321522447779 10442677522567982283671669)
                  ·
                    refine ⟨979001017740748339094219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10442677522567982283671669 979001017740748339094219)
                    ·
                      rfl

theorem cell23_5719793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_5719793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719793 prefixEnd_5719793 := by exact prefixLift 5719793
  have htrace : WordTrace (prefixWord ++ tailWord_5719793) baseStart_5719793 baseEnd_5719793 := by
    simpa [prefixWord, tailWord_5719793, baseEnd_5719793] using wordTrace_append hprefix tailTrace_5719793
  have hstable : (prefixWord ++ tailWord_5719793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719793).length < 2 ^ (prefixWord ++ tailWord_5719793).sum := by decide
  have hdescent : baseEnd_5719793 < baseStart_5719793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719809 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_5719809 : Nat := 118140960795 + 5719809 * 2 ^ 59
def prefixEnd_5719809 : Nat := 4983230072969 + 3 ^ 40 * 5719809 * 2
def baseEnd_5719809 : Nat := 2937011268912716954682583

theorem tailTrace_5719809 : CollatzResearch.WordTrace tailWord_5719809 prefixEnd_5719809 2937011268912716954682583 := by
  unfold tailWord_5719809
  simp only [CollatzResearch.WordTrace]
  refine ⟨208618572935116333450066481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139079048623410888966710987 208618572935116333450066481)
  ·
    refine ⟨156463929701337250087549861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208618572935116333450066481 156463929701337250087549861)
    ·
      refine ⟨29336986819000734391415599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156463929701337250087549861 29336986819000734391415599)
      ·
        refine ⟨44005480228501101587123399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29336986819000734391415599 44005480228501101587123399)
        ·
          refine ⟨66008220342751652380685099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44005480228501101587123399 66008220342751652380685099)
          ·
            refine ⟨99012330514127478571027649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66008220342751652380685099 99012330514127478571027649)
            ·
              refine ⟨74259247885595608928270737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99012330514127478571027649 74259247885595608928270737)
              ·
                refine ⟨55694435914196706696203053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74259247885595608928270737 55694435914196706696203053)
                ·
                  refine ⟨20885413467823765011076145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55694435914196706696203053 20885413467823765011076145)
                  ·
                    refine ⟨15664060100867823758307109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20885413467823765011076145 15664060100867823758307109)
                    ·
                      refine ⟨2937011268912716954682583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15664060100867823758307109 2937011268912716954682583)
                      ·
                        rfl

theorem cell23_5719809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_5719809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719809 prefixEnd_5719809 := by exact prefixLift 5719809
  have htrace : WordTrace (prefixWord ++ tailWord_5719809) baseStart_5719809 baseEnd_5719809 := by
    simpa [prefixWord, tailWord_5719809, baseEnd_5719809] using wordTrace_append hprefix tailTrace_5719809
  have hstable : (prefixWord ++ tailWord_5719809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719809).length < 2 ^ (prefixWord ++ tailWord_5719809).sum := by decide
  have hdescent : baseEnd_5719809 < baseStart_5719809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719856 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 7, 3, 2]
def baseStart_5719856 : Nat := 118140960795 + 5719856 * 2 ^ 59
def prefixEnd_5719856 : Nat := 4983230072969 + 3 ^ 40 * 5719856 * 2
def baseEnd_5719856 : Nat := 2937035402503478270794867

theorem tailTrace_5719856 : CollatzResearch.WordTrace tailWord_5719856 prefixEnd_5719856 2937035402503478270794867 := by
  unfold tailWord_5719856
  simp only [CollatzResearch.WordTrace]
  refine ⟨104310143582973030238513711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139080191443964040318018281 104310143582973030238513711)
  ·
    refine ⟨156465215374459545357770567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104310143582973030238513711 156465215374459545357770567)
    ·
      refine ⟨234697823061689318036655851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156465215374459545357770567 234697823061689318036655851)
      ·
        refine ⟨352046734592533977054983777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234697823061689318036655851 352046734592533977054983777)
        ·
          refine ⟨264035050944400482791237833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352046734592533977054983777 264035050944400482791237833)
          ·
            refine ⟨198026288208300362093428375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264035050944400482791237833 198026288208300362093428375)
            ·
              refine ⟨297039432312450543140142563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198026288208300362093428375 297039432312450543140142563)
              ·
                refine ⟨445559148468675814710213845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297039432312450543140142563 445559148468675814710213845)
                ·
                  refine ⟨10442792542234589407270637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 445559148468675814710213845 10442792542234589407270637)
                  ·
                    refine ⟨3916047203337971027726489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10442792542234589407270637 3916047203337971027726489)
                    ·
                      refine ⟨2937035402503478270794867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916047203337971027726489 2937035402503478270794867)
                      ·
                        rfl

theorem cell23_5719856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 3, 2].length) (baseStart_5719856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719856 prefixEnd_5719856 := by exact prefixLift 5719856
  have htrace : WordTrace (prefixWord ++ tailWord_5719856) baseStart_5719856 baseEnd_5719856 := by
    simpa [prefixWord, tailWord_5719856, baseEnd_5719856] using wordTrace_append hprefix tailTrace_5719856
  have hstable : (prefixWord ++ tailWord_5719856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719856).length < 2 ^ (prefixWord ++ tailWord_5719856).sum := by decide
  have hdescent : baseEnd_5719856 < baseStart_5719856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719879 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 2, 6]
def baseStart_5719879 : Nat := 118140960795 + 5719879 * 2 ^ 59
def prefixEnd_5719879 : Nat := 4983230072969 + 3 ^ 40 * 5719879 * 2
def baseEnd_5719879 : Nat := 979015737519510560269087

theorem tailTrace_5719879 : CollatzResearch.WordTrace tailWord_5719879 prefixEnd_5719879 979015737519510560269087 := by
  unfold tailWord_5719879
  simp only [CollatzResearch.WordTrace]
  refine ⟨208621126044862735405114691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139080750696575156936743127 208621126044862735405114691)
  ·
    refine ⟨312931689067294103107672037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208621126044862735405114691 312931689067294103107672037)
    ·
      refine ⟨58674691700117644332688507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312931689067294103107672037 58674691700117644332688507)
      ·
        refine ⟨88012037550176466499032761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58674691700117644332688507 88012037550176466499032761)
        ·
          refine ⟨66009028162632349874274571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88012037550176466499032761 66009028162632349874274571)
          ·
            refine ⟨99013542243948524811411857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66009028162632349874274571 99013542243948524811411857)
            ·
              refine ⟨74260156682961393608558893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99013542243948524811411857 74260156682961393608558893)
              ·
                refine ⟨27847558756110522603209585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74260156682961393608558893 27847558756110522603209585)
                ·
                  refine ⟨20885669067082891952407189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27847558756110522603209585 20885669067082891952407189)
                  ·
                    refine ⟨979015737519510560269087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20885669067082891952407189 979015737519510560269087)
                    ·
                      rfl

theorem cell23_5719879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_5719879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719879 prefixEnd_5719879 := by exact prefixLift 5719879
  have htrace : WordTrace (prefixWord ++ tailWord_5719879) baseStart_5719879 baseEnd_5719879 := by
    simpa [prefixWord, tailWord_5719879, baseEnd_5719879] using wordTrace_append hprefix tailTrace_5719879
  have hstable : (prefixWord ++ tailWord_5719879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719879).length < 2 ^ (prefixWord ++ tailWord_5719879).sum := by decide
  have hdescent : baseEnd_5719879 < baseStart_5719879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719880 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_5719880 : Nat := 118140960795 + 5719880 * 2 ^ 59
def prefixEnd_5719880 : Nat := 4983230072969 + 3 ^ 40 * 5719880 * 2
def baseEnd_5719880 : Nat := 2937047726039186176894757

theorem tailTrace_5719880 : CollatzResearch.WordTrace tailWord_5719880 prefixEnd_5719880 2937047726039186176894757 := by
  unfold tailWord_5719880
  simp only [CollatzResearch.WordTrace]
  refine ⟨104310581258929556287950547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139080775011906075050600729 104310581258929556287950547)
  ·
    refine ⟨156465871888394334431925821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104310581258929556287950547 156465871888394334431925821)
    ·
      refine ⟨58674701958147875411972183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156465871888394334431925821 58674701958147875411972183)
      ·
        refine ⟨88012052937221813117958275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58674701958147875411972183 88012052937221813117958275)
        ·
          refine ⟨132018079405832719676937413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88012052937221813117958275 132018079405832719676937413)
          ·
            refine ⟨24753389888593634939425765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132018079405832719676937413 24753389888593634939425765)
            ·
              refine ⟨4641260604111306551142331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24753389888593634939425765 4641260604111306551142331)
              ·
                refine ⟨6961890906166959826713497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641260604111306551142331 6961890906166959826713497)
                ·
                  refine ⟨5221418179625219870035123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6961890906166959826713497 5221418179625219870035123)
                  ·
                    refine ⟨7832127269437829805052685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5221418179625219870035123 7832127269437829805052685)
                    ·
                      refine ⟨2937047726039186176894757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832127269437829805052685 2937047726039186176894757)
                      ·
                        rfl

theorem cell23_5719880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_5719880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719880 prefixEnd_5719880 := by exact prefixLift 5719880
  have htrace : WordTrace (prefixWord ++ tailWord_5719880) baseStart_5719880 baseEnd_5719880 := by
    simpa [prefixWord, tailWord_5719880, baseEnd_5719880] using wordTrace_append hprefix tailTrace_5719880
  have hstable : (prefixWord ++ tailWord_5719880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719880).length < 2 ^ (prefixWord ++ tailWord_5719880).sum := by decide
  have hdescent : baseEnd_5719880 < baseStart_5719880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719890 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_5719890 : Nat := 118140960795 + 5719890 * 2 ^ 59
def prefixEnd_5719890 : Nat := 4983230072969 + 3 ^ 40 * 5719890 * 2
def baseEnd_5719890 : Nat := 2937052860845731137769711

theorem tailTrace_5719890 : CollatzResearch.WordTrace tailWord_5719890 prefixEnd_5719890 2937052860845731137769711 := by
  unfold tailWord_5719890
  simp only [CollatzResearch.WordTrace]
  refine ⟨52155381811955721070941281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139081018165215256189176749 52155381811955721070941281)
  ·
    refine ⟨39116536358966790803205961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52155381811955721070941281 39116536358966790803205961)
    ·
      refine ⟨29337402269225093102404471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39116536358966790803205961 29337402269225093102404471)
      ·
        refine ⟨44006103403837639653606707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29337402269225093102404471 44006103403837639653606707)
        ·
          refine ⟨66009155105756459480410061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44006103403837639653606707 66009155105756459480410061)
          ·
            refine ⟨24753433164658672305153773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66009155105756459480410061 24753433164658672305153773)
            ·
              refine ⟨9282537436747002114432665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24753433164658672305153773 9282537436747002114432665)
              ·
                refine ⟨6961903077560251585824499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9282537436747002114432665 6961903077560251585824499)
                ·
                  refine ⟨10442854616340377378736749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961903077560251585824499 10442854616340377378736749)
                  ·
                    refine ⟨3916070481127641517026281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10442854616340377378736749 3916070481127641517026281)
                    ·
                      refine ⟨2937052860845731137769711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916070481127641517026281 2937052860845731137769711)
                      ·
                        rfl

theorem cell23_5719890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_5719890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719890 prefixEnd_5719890 := by exact prefixLift 5719890
  have htrace : WordTrace (prefixWord ++ tailWord_5719890) baseStart_5719890 baseEnd_5719890 := by
    simpa [prefixWord, tailWord_5719890, baseEnd_5719890] using wordTrace_append hprefix tailTrace_5719890
  have hstable : (prefixWord ++ tailWord_5719890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719890).length < 2 ^ (prefixWord ++ tailWord_5719890).sum := by decide
  have hdescent : baseEnd_5719890 < baseStart_5719890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719903 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 1, 4, 2]
def baseStart_5719903 : Nat := 118140960795 + 5719903 * 2 ^ 59
def prefixEnd_5719903 : Nat := 4983230072969 + 3 ^ 40 * 5719903 * 2
def baseEnd_5719903 : Nat := 2937059536094239586907151

theorem tailTrace_5719903 : CollatzResearch.WordTrace tailWord_5719903 prefixEnd_5719903 2937059536094239586907151 := by
  unfold tailWord_5719903
  simp only [CollatzResearch.WordTrace]
  refine ⟨208622001396775787503988363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139081334264517191669325575 208622001396775787503988363)
  ·
    refine ⟨312933002095163681255982545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208622001396775787503988363 312933002095163681255982545)
    ·
      refine ⟨234699751571372760941986909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312933002095163681255982545 234699751571372760941986909)
      ·
        refine ⟨88012406839264785353245091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234699751571372760941986909 88012406839264785353245091)
        ·
          refine ⟨132018610258897178029867637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88012406839264785353245091 132018610258897178029867637)
          ·
            refine ⟨12376744711771610440300091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132018610258897178029867637 12376744711771610440300091)
            ·
              refine ⟨18565117067657415660450137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12376744711771610440300091 18565117067657415660450137)
              ·
                refine ⟨13923837800743061745337603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18565117067657415660450137 13923837800743061745337603)
                ·
                  refine ⟨20885756701114592618006405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13923837800743061745337603 20885756701114592618006405)
                  ·
                    refine ⟨3916079381458986115876201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20885756701114592618006405 3916079381458986115876201)
                    ·
                      refine ⟨2937059536094239586907151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916079381458986115876201 2937059536094239586907151)
                      ·
                        rfl

theorem cell23_5719903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_5719903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719903 prefixEnd_5719903 := by exact prefixLift 5719903
  have htrace : WordTrace (prefixWord ++ tailWord_5719903) baseStart_5719903 baseEnd_5719903 := by
    simpa [prefixWord, tailWord_5719903, baseEnd_5719903] using wordTrace_append hprefix tailTrace_5719903
  have hstable : (prefixWord ++ tailWord_5719903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719903).length < 2 ^ (prefixWord ++ tailWord_5719903).sum := by decide
  have hdescent : baseEnd_5719903 < baseStart_5719903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719907 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 1, 3, 2]
def baseStart_5719907 : Nat := 118140960795 + 5719907 * 2 ^ 59
def prefixEnd_5719907 : Nat := 4983230072969 + 3 ^ 40 * 5719907 * 2
def baseEnd_5719907 : Nat := 2937061590016857571257133

theorem tailTrace_5719907 : CollatzResearch.WordTrace tailWord_5719907 prefixEnd_5719907 2937061590016857571257133 := by
  unfold tailWord_5719907
  simp only [CollatzResearch.WordTrace]
  refine ⟨208622147288761296187133975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139081431525840864124755983 208622147288761296187133975)
  ·
    refine ⟨312933220933141944280700963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208622147288761296187133975 312933220933141944280700963)
    ·
      refine ⟨469399831399712916421051445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312933220933141944280700963 469399831399712916421051445)
      ·
        refine ⟨44006234193723085914473573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 469399831399712916421051445 44006234193723085914473573)
        ·
          refine ⟨8251168911323078608963795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44006234193723085914473573 8251168911323078608963795)
          ·
            refine ⟨12376753366984617913445693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251168911323078608963795 12376753366984617913445693)
            ·
              refine ⟨4641282512619231717542135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12376753366984617913445693 4641282512619231717542135)
              ·
                refine ⟨6961923768928847576313203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641282512619231717542135 6961923768928847576313203)
                ·
                  refine ⟨10442885653393271364469805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961923768928847576313203 10442885653393271364469805)
                  ·
                    refine ⟨3916082120022476761676177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10442885653393271364469805 3916082120022476761676177)
                    ·
                      refine ⟨2937061590016857571257133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916082120022476761676177 2937061590016857571257133)
                      ·
                        rfl

theorem cell23_5719907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_5719907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719907 prefixEnd_5719907 := by exact prefixLift 5719907
  have htrace : WordTrace (prefixWord ++ tailWord_5719907) baseStart_5719907 baseEnd_5719907 := by
    simpa [prefixWord, tailWord_5719907, baseEnd_5719907] using wordTrace_append hprefix tailTrace_5719907
  have hstable : (prefixWord ++ tailWord_5719907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719907).length < 2 ^ (prefixWord ++ tailWord_5719907).sum := by decide
  have hdescent : baseEnd_5719907 < baseStart_5719907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719936 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_5719936 : Nat := 118140960795 + 5719936 * 2 ^ 59
def prefixEnd_5719936 : Nat := 4983230072969 + 3 ^ 40 * 5719936 * 2
def baseEnd_5719936 : Nat := 2937076480955837957794499

theorem tailTrace_5719936 : CollatzResearch.WordTrace tailWord_5719936 prefixEnd_5719936 2937076480955837957794499 := by
  unfold tailWord_5719936
  simp only [CollatzResearch.WordTrace]
  refine ⟨104311602502828117069969831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139082136670437489426626441 104311602502828117069969831)
  ·
    refine ⟨156467403754242175604954747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104311602502828117069969831 156467403754242175604954747)
    ·
      refine ⟨234701105631363263407432121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156467403754242175604954747 234701105631363263407432121)
      ·
        refine ⟨176025829223522447555574091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234701105631363263407432121 176025829223522447555574091)
        ·
          refine ⟨264038743835283671333361137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176025829223522447555574091 264038743835283671333361137)
          ·
            refine ⟨198029057876462753500020853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264038743835283671333361137 198029057876462753500020853)
            ·
              refine ⟨18565224175918383140626955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198029057876462753500020853 18565224175918383140626955)
              ·
                refine ⟨27847836263877574710940433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18565224175918383140626955 27847836263877574710940433)
                ·
                  refine ⟨20885877197908181033205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27847836263877574710940433 20885877197908181033205325)
                  ·
                    refine ⟨7832203949215567887451997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20885877197908181033205325 7832203949215567887451997)
                    ·
                      refine ⟨2937076480955837957794499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832203949215567887451997 2937076480955837957794499)
                      ·
                        rfl

theorem cell23_5719936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_5719936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719936 prefixEnd_5719936 := by exact prefixLift 5719936
  have htrace : WordTrace (prefixWord ++ tailWord_5719936) baseStart_5719936 baseEnd_5719936 := by
    simpa [prefixWord, tailWord_5719936, baseEnd_5719936] using wordTrace_append hprefix tailTrace_5719936
  have hstable : (prefixWord ++ tailWord_5719936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719936).length < 2 ^ (prefixWord ++ tailWord_5719936).sum := by decide
  have hdescent : baseEnd_5719936 < baseStart_5719936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719937 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5719937 : Nat := 118140960795 + 5719937 * 2 ^ 59
def prefixEnd_5719937 : Nat := 4983230072969 + 3 ^ 40 * 5719937 * 2
def baseEnd_5719937 : Nat := 2937076994436492453881995

theorem tailTrace_5719937 : CollatzResearch.WordTrace tailWord_5719937 prefixEnd_5719937 2937076994436492453881995 := by
  unfold tailWord_5719937
  simp only [CollatzResearch.WordTrace]
  refine ⟨208623241478652611310726065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139082160985768407540484043 208623241478652611310726065)
  ·
    refine ⟨156467431108989458483044549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208623241478652611310726065 156467431108989458483044549)
    ·
      refine ⟨29337643332935523465570853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156467431108989458483044549 29337643332935523465570853)
      ·
        refine ⟨5500808124925410649794535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29337643332935523465570853 5500808124925410649794535)
        ·
          refine ⟨8251212187388115974691803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500808124925410649794535 8251212187388115974691803)
          ·
            refine ⟨12376818281082173962037705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251212187388115974691803 12376818281082173962037705)
            ·
              refine ⟨9282613710811630471528279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12376818281082173962037705 9282613710811630471528279)
              ·
                refine ⟨13923920566217445707292419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9282613710811630471528279 13923920566217445707292419)
                ·
                  refine ⟨20885880849326168560938629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13923920566217445707292419 20885880849326168560938629)
                  ·
                    refine ⟨3916102659248656605175993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20885880849326168560938629 3916102659248656605175993)
                    ·
                      refine ⟨2937076994436492453881995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916102659248656605175993 2937076994436492453881995)
                      ·
                        rfl

theorem cell23_5719937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5719937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719937 prefixEnd_5719937 := by exact prefixLift 5719937
  have htrace : WordTrace (prefixWord ++ tailWord_5719937) baseStart_5719937 baseEnd_5719937 := by
    simpa [prefixWord, tailWord_5719937, baseEnd_5719937] using wordTrace_append hprefix tailTrace_5719937
  have hstable : (prefixWord ++ tailWord_5719937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719937).length < 2 ^ (prefixWord ++ tailWord_5719937).sum := by decide
  have hdescent : baseEnd_5719937 < baseStart_5719937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719958 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5719958 : Nat := 118140960795 + 5719958 * 2 ^ 59
def prefixEnd_5719958 : Nat := 4983230072969 + 3 ^ 40 * 5719958 * 2
def baseEnd_5719958 : Nat := 2937087777530236871719399

theorem tailTrace_5719958 : CollatzResearch.WordTrace tailWord_5719958 prefixEnd_5719958 2937087777530236871719399 := by
  unfold tailWord_5719958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039000463223533243577533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139082671607717687931493685 13039000463223533243577533)
  ·
    refine ⟨4889625173708824966341575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13039000463223533243577533 4889625173708824966341575)
    ·
      refine ⟨7334437760563237449512363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4889625173708824966341575 7334437760563237449512363)
      ·
        refine ⟨11001656640844856174268545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334437760563237449512363 11001656640844856174268545)
        ·
          refine ⟨8251242480633642130701409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11001656640844856174268545 8251242480633642130701409)
          ·
            refine ⟨6188431860475231598026057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8251242480633642130701409 6188431860475231598026057)
            ·
              refine ⟨4641323895356423698519543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188431860475231598026057 4641323895356423698519543)
              ·
                refine ⟨6961985843034635547779315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641323895356423698519543 6961985843034635547779315)
                ·
                  refine ⟨10442978764551953321668973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6961985843034635547779315 10442978764551953321668973)
                  ·
                    refine ⟨3916117036706982495625865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10442978764551953321668973 3916117036706982495625865)
                    ·
                      refine ⟨2937087777530236871719399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916117036706982495625865 2937087777530236871719399)
                      ·
                        rfl

theorem cell23_5719958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5719958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719958 prefixEnd_5719958 := by exact prefixLift 5719958
  have htrace : WordTrace (prefixWord ++ tailWord_5719958) baseStart_5719958 baseEnd_5719958 := by
    simpa [prefixWord, tailWord_5719958, baseEnd_5719958] using wordTrace_append hprefix tailTrace_5719958
  have hstable : (prefixWord ++ tailWord_5719958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719958).length < 2 ^ (prefixWord ++ tailWord_5719958).sum := by decide
  have hdescent : baseEnd_5719958 < baseStart_5719958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5719993 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 2, 4, 2]
def baseStart_5719993 : Nat := 118140960795 + 5719993 * 2 ^ 59
def prefixEnd_5719993 : Nat := 4983230072969 + 3 ^ 40 * 5719993 * 2
def baseEnd_5719993 : Nat := 2937105749353144234781737

theorem tailTrace_5719993 : CollatzResearch.WordTrace tailWord_5719993 prefixEnd_5719993 2937105749353144234781737 := by
  unfold tailWord_5719993
  simp only [CollatzResearch.WordTrace]
  refine ⟨208625283966449732874764633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139083522644299821916509755 208625283966449732874764633)
  ·
    refine ⟨156468962974837299656073475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208625283966449732874764633 156468962974837299656073475)
    ·
      refine ⟨234703444462255949484110213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156468962974837299656073475 234703444462255949484110213)
      ·
        refine ⟨44006895836672990528270665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234703444462255949484110213 44006895836672990528270665)
        ·
          refine ⟨33005171877504742896202999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44006895836672990528270665 33005171877504742896202999)
          ·
            refine ⟨49507757816257114344304499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33005171877504742896202999 49507757816257114344304499)
            ·
              refine ⟨74261636724385671516456749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49507757816257114344304499 74261636724385671516456749)
              ·
                refine ⟨27848113771644626818671281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74261636724385671516456749 27848113771644626818671281)
                ·
                  refine ⟨20886085328733470114003461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27848113771644626818671281 20886085328733470114003461)
                  ·
                    refine ⟨3916140999137525646375649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20886085328733470114003461 3916140999137525646375649)
                    ·
                      refine ⟨2937105749353144234781737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916140999137525646375649 2937105749353144234781737)
                      ·
                        rfl

theorem cell23_5719993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_5719993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5719993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5719993 prefixEnd_5719993 := by exact prefixLift 5719993
  have htrace : WordTrace (prefixWord ++ tailWord_5719993) baseStart_5719993 baseEnd_5719993 := by
    simpa [prefixWord, tailWord_5719993, baseEnd_5719993] using wordTrace_append hprefix tailTrace_5719993
  have hstable : (prefixWord ++ tailWord_5719993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5719993).length < 2 ^ (prefixWord ++ tailWord_5719993).sum := by decide
  have hdescent : baseEnd_5719993 < baseStart_5719993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5719993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720083 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 4]
def baseStart_5720083 : Nat := 118140960795 + 5720083 * 2 ^ 59
def prefixEnd_5720083 : Nat := 4983230072969 + 3 ^ 40 * 5720083 * 2
def baseEnd_5720083 : Nat := 2937151962612048882656323

theorem tailTrace_5720083 : CollatzResearch.WordTrace tailWord_5720083 prefixEnd_5720083 2937151962612048882656323 := by
  unfold tailWord_5720083
  simp only [CollatzResearch.WordTrace]
  refine ⟨208628566536123678245540903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139085711024082452163693935 208628566536123678245540903)
  ·
    refine ⟨312942849804185517368311355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208628566536123678245540903 312942849804185517368311355)
    ·
      refine ⟨469414274706278276052467033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312942849804185517368311355 469414274706278276052467033)
      ·
        refine ⟨352060706029708707039350275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469414274706278276052467033 352060706029708707039350275)
        ·
          refine ⟨528091059044563060559025413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352060706029708707039350275 528091059044563060559025413)
          ·
            refine ⟨99017073570855573854817265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 528091059044563060559025413 99017073570855573854817265)
            ·
              refine ⟨74262805178141680391112949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99017073570855573854817265 74262805178141680391112949)
              ·
                refine ⟨6962137985450782536666839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74262805178141680391112949 6962137985450782536666839)
                ·
                  refine ⟨10443206978176173805000259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962137985450782536666839 10443206978176173805000259)
                  ·
                    refine ⟨15664810467264260707500389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10443206978176173805000259 15664810467264260707500389)
                    ·
                      refine ⟨2937151962612048882656323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15664810467264260707500389 2937151962612048882656323)
                      ·
                        rfl

theorem cell23_5720083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_5720083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720083 prefixEnd_5720083 := by exact prefixLift 5720083
  have htrace : WordTrace (prefixWord ++ tailWord_5720083) baseStart_5720083 baseEnd_5720083 := by
    simpa [prefixWord, tailWord_5720083, baseEnd_5720083] using wordTrace_append hprefix tailTrace_5720083
  have hstable : (prefixWord ++ tailWord_5720083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720083).length < 2 ^ (prefixWord ++ tailWord_5720083).sum := by decide
  have hdescent : baseEnd_5720083 < baseStart_5720083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720110 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5720110 : Nat := 118140960795 + 5720110 * 2 ^ 59
def prefixEnd_5720110 : Nat := 4983230072969 + 3 ^ 40 * 5720110 * 2
def baseEnd_5720110 : Nat := 979055275529906759006233

theorem tailTrace_5720110 : CollatzResearch.WordTrace tailWord_5720110 prefixEnd_5720110 979055275529906759006233 := by
  unfold tailWord_5720110
  simp only [CollatzResearch.WordTrace]
  refine ⟨26078693913378232732096723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139086367538017241237849189 26078693913378232732096723)
  ·
    refine ⟨39118040870067349098145085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26078693913378232732096723 39118040870067349098145085)
    ·
      refine ⟨14669265326275255911804407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39118040870067349098145085 14669265326275255911804407)
      ·
        refine ⟨22003897989412883867706611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14669265326275255911804407 22003897989412883867706611)
        ·
          refine ⟨33005846984119325801559917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22003897989412883867706611 33005846984119325801559917)
          ·
            refine ⟨12377192619044747175584969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33005846984119325801559917 12377192619044747175584969)
            ·
              refine ⟨9282894464283560381688727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12377192619044747175584969 9282894464283560381688727)
              ·
                refine ⟨13924341696425340572533091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9282894464283560381688727 13924341696425340572533091)
                ·
                  refine ⟨20886512544638010858799637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13924341696425340572533091 20886512544638010858799637)
                  ·
                    refine ⟨979055275529906759006233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20886512544638010858799637 979055275529906759006233)
                    ·
                      rfl

theorem cell23_5720110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5720110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720110 prefixEnd_5720110 := by exact prefixLift 5720110
  have htrace : WordTrace (prefixWord ++ tailWord_5720110) baseStart_5720110 baseEnd_5720110 := by
    simpa [prefixWord, tailWord_5720110, baseEnd_5720110] using wordTrace_append hprefix tailTrace_5720110
  have hstable : (prefixWord ++ tailWord_5720110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720110).length < 2 ^ (prefixWord ++ tailWord_5720110).sum := by decide
  have hdescent : baseEnd_5720110 < baseStart_5720110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720113 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5720113 : Nat := 118140960795 + 5720113 * 2 ^ 59
def prefixEnd_5720113 : Nat := 4983230072969 + 3 ^ 40 * 5720113 * 2
def baseEnd_5720113 : Nat := 2937167367031683765281185

theorem tailTrace_5720113 : CollatzResearch.WordTrace tailWord_5720113 prefixEnd_5720113 2937167367031683765281185 := by
  unfold tailWord_5720113
  simp only [CollatzResearch.WordTrace]
  refine ⟨208629660726014993369132993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139086440484009995579421995 208629660726014993369132993)
  ·
    refine ⟨156472245544511245026849745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208629660726014993369132993 156472245544511245026849745)
    ·
      refine ⟨117354184158383433770137309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156472245544511245026849745 117354184158383433770137309)
      ·
        refine ⟨44007819059393787663801491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117354184158383433770137309 44007819059393787663801491)
        ·
          refine ⟨66011728589090681495702237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44007819059393787663801491 66011728589090681495702237)
          ·
            refine ⟨24754398220909005560888339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66011728589090681495702237 24754398220909005560888339)
            ·
              refine ⟨37131597331363508341332509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24754398220909005560888339 37131597331363508341332509)
              ·
                refine ⟨13924348999261315627999691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37131597331363508341332509 13924348999261315627999691)
                ·
                  refine ⟨20886523498891973441999537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13924348999261315627999691 20886523498891973441999537)
                  ·
                    refine ⟨15664892624168980081499653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20886523498891973441999537 15664892624168980081499653)
                    ·
                      refine ⟨2937167367031683765281185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15664892624168980081499653 2937167367031683765281185)
                      ·
                        rfl

theorem cell23_5720113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5720113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720113 prefixEnd_5720113 := by exact prefixLift 5720113
  have htrace : WordTrace (prefixWord ++ tailWord_5720113) baseStart_5720113 baseEnd_5720113 := by
    simpa [prefixWord, tailWord_5720113, baseEnd_5720113] using wordTrace_append hprefix tailTrace_5720113
  have hstable : (prefixWord ++ tailWord_5720113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720113).length < 2 ^ (prefixWord ++ tailWord_5720113).sum := by decide
  have hdescent : baseEnd_5720113 < baseStart_5720113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720134 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5720134 : Nat := 118140960795 + 5720134 * 2 ^ 59
def prefixEnd_5720134 : Nat := 4983230072969 + 3 ^ 40 * 5720134 * 2
def baseEnd_5720134 : Nat := 2937178150125428183118589

theorem tailTrace_5720134 : CollatzResearch.WordTrace tailWord_5720134 prefixEnd_5720134 2937178150125428183118589 := by
  unfold tailWord_5720134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519700833091841061113983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139086951105959275970431637 6519700833091841061113983)
  ·
    refine ⟨9779551249637761591670975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519700833091841061113983 9779551249637761591670975)
    ·
      refine ⟨14669326874456642387506463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9779551249637761591670975 14669326874456642387506463)
      ·
        refine ⟨22003990311684963581259695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14669326874456642387506463 22003990311684963581259695)
        ·
          refine ⟨33005985467527445371889543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22003990311684963581259695 33005985467527445371889543)
          ·
            refine ⟨49508978201291168057834315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33005985467527445371889543 49508978201291168057834315)
            ·
              refine ⟨74263467301936752086751473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49508978201291168057834315 74263467301936752086751473)
              ·
                refine ⟨55697600476452564065063605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74263467301936752086751473 55697600476452564065063605)
                ·
                  refine ⟨5221650044667427881099713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55697600476452564065063605 5221650044667427881099713)
                  ·
                    refine ⟨3916237533500570910824785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5221650044667427881099713 3916237533500570910824785)
                    ·
                      refine ⟨2937178150125428183118589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916237533500570910824785 2937178150125428183118589)
                      ·
                        rfl

theorem cell23_5720134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5720134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720134 prefixEnd_5720134 := by exact prefixLift 5720134
  have htrace : WordTrace (prefixWord ++ tailWord_5720134) baseStart_5720134 baseEnd_5720134 := by
    simpa [prefixWord, tailWord_5720134, baseEnd_5720134] using wordTrace_append hprefix tailTrace_5720134
  have hstable : (prefixWord ++ tailWord_5720134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720134).length < 2 ^ (prefixWord ++ tailWord_5720134).sum := by decide
  have hdescent : baseEnd_5720134 < baseStart_5720134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720136 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_5720136 : Nat := 118140960795 + 5720136 * 2 ^ 59
def prefixEnd_5720136 : Nat := 4983230072969 + 3 ^ 40 * 5720136 * 2
def baseEnd_5720136 : Nat := 979059725695579058431193

theorem tailTrace_5720136 : CollatzResearch.WordTrace tailWord_5720136 prefixEnd_5720136 979059725695579058431193 := by
  unfold tailWord_5720136
  simp only [CollatzResearch.WordTrace]
  refine ⟨104315249802465834148610131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139086999736621112198146841 104315249802465834148610131)
  ·
    refine ⟨156472874703698751222915197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104315249802465834148610131 156472874703698751222915197)
    ·
      refine ⟨58677328013887031708593199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156472874703698751222915197 58677328013887031708593199)
      ·
        refine ⟨88015992020830547562889799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58677328013887031708593199 88015992020830547562889799)
        ·
          refine ⟨132023988031245821344334699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88015992020830547562889799 132023988031245821344334699)
          ·
            refine ⟨198035982046868732016502049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132023988031245821344334699 198035982046868732016502049)
            ·
              refine ⟨148526986535151549012376537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198035982046868732016502049 148526986535151549012376537)
              ·
                refine ⟨111395239901363661759282403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148526986535151549012376537 111395239901363661759282403)
                ·
                  refine ⟨167092859852045492638923605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111395239901363661759282403 167092859852045492638923605)
                  ·
                    refine ⟨979059725695579058431193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 167092859852045492638923605 979059725695579058431193)
                    ·
                      rfl

theorem cell23_5720136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_5720136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720136 prefixEnd_5720136 := by exact prefixLift 5720136
  have htrace : WordTrace (prefixWord ++ tailWord_5720136) baseStart_5720136 baseEnd_5720136 := by
    simpa [prefixWord, tailWord_5720136, baseEnd_5720136] using wordTrace_append hprefix tailTrace_5720136
  have hstable : (prefixWord ++ tailWord_5720136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720136).length < 2 ^ (prefixWord ++ tailWord_5720136).sum := by decide
  have hdescent : baseEnd_5720136 < baseStart_5720136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720177 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 1, 3, 2]
def baseStart_5720177 : Nat := 118140960795 + 5720177 * 2 ^ 59
def prefixEnd_5720177 : Nat := 4983230072969 + 3 ^ 40 * 5720177 * 2
def baseEnd_5720177 : Nat := 2937200229793571514880891

theorem tailTrace_5720177 : CollatzResearch.WordTrace tailWord_5720177 prefixEnd_5720177 2937200229793571514880891 := by
  unfold tailWord_5720177
  simp only [CollatzResearch.WordTrace]
  refine ⟨208631994997783132299462785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139087996665188754866308523 208631994997783132299462785)
  ·
    refine ⟨156473996248337349224597089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208631994997783132299462785 156473996248337349224597089)
    ·
      refine ⟨117355497186253011918447817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156473996248337349224597089 117355497186253011918447817)
      ·
        refine ⟨88016622889689758938835863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117355497186253011918447817 88016622889689758938835863)
        ·
          refine ⟨132024934334534638408253795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88016622889689758938835863 132024934334534638408253795)
          ·
            refine ⟨198037401501801957612380693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132024934334534638408253795 198037401501801957612380693)
            ·
              refine ⟨9283003195396966763080345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198037401501801957612380693 9283003195396966763080345)
              ·
                refine ⟨6962252396547725072310259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9283003195396966763080345 6962252396547725072310259)
                ·
                  refine ⟨10443378594821587608465389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962252396547725072310259 10443378594821587608465389)
                  ·
                    refine ⟨3916266973058095353174521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10443378594821587608465389 3916266973058095353174521)
                    ·
                      refine ⟨2937200229793571514880891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916266973058095353174521 2937200229793571514880891)
                      ·
                        rfl

theorem cell23_5720177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_5720177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720177 prefixEnd_5720177 := by exact prefixLift 5720177
  have htrace : WordTrace (prefixWord ++ tailWord_5720177) baseStart_5720177 baseEnd_5720177 := by
    simpa [prefixWord, tailWord_5720177, baseEnd_5720177] using wordTrace_append hprefix tailTrace_5720177
  have hstable : (prefixWord ++ tailWord_5720177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720177).length < 2 ^ (prefixWord ++ tailWord_5720177).sum := by decide
  have hdescent : baseEnd_5720177 < baseStart_5720177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720210 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5720210 : Nat := 118140960795 + 5720210 * 2 ^ 59
def prefixEnd_5720210 : Nat := 4983230072969 + 3 ^ 40 * 5720210 * 2
def baseEnd_5720210 : Nat := 2937217174655169885768239

theorem tailTrace_5720210 : CollatzResearch.WordTrace tailWord_5720210 prefixEnd_5720210 2937217174655169885768239 := by
  unfold tailWord_5720210
  simp only [CollatzResearch.WordTrace]
  refine ⟨52158299651665894733853521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139088799071109052623609389 52158299651665894733853521)
  ·
    refine ⟨39118724738749421050390141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52158299651665894733853521 39118724738749421050390141)
    ·
      refine ⟨14669521777031032893896303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39118724738749421050390141 14669521777031032893896303)
      ·
        refine ⟨22004282665546549340844455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14669521777031032893896303 22004282665546549340844455)
        ·
          refine ⟨33006423998319824011266683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22004282665546549340844455 33006423998319824011266683)
          ·
            refine ⟨49509635997479736016900025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33006423998319824011266683 49509635997479736016900025)
            ·
              refine ⟨37132226998109802012675019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49509635997479736016900025 37132226998109802012675019)
              ·
                refine ⟨55698340497164703019012529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37132226998109802012675019 55698340497164703019012529)
                ·
                  refine ⟨41773755372873527264259397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55698340497164703019012529 41773755372873527264259397)
                  ·
                    refine ⟨7832579132413786362048637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41773755372873527264259397 7832579132413786362048637)
                    ·
                      refine ⟨2937217174655169885768239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832579132413786362048637 2937217174655169885768239)
                      ·
                        rfl

theorem cell23_5720210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5720210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720210 prefixEnd_5720210 := by exact prefixLift 5720210
  have htrace : WordTrace (prefixWord ++ tailWord_5720210) baseStart_5720210 baseEnd_5720210 := by
    simpa [prefixWord, tailWord_5720210, baseEnd_5720210] using wordTrace_append hprefix tailTrace_5720210
  have hstable : (prefixWord ++ tailWord_5720210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720210).length < 2 ^ (prefixWord ++ tailWord_5720210).sum := by decide
  have hdescent : baseEnd_5720210 < baseStart_5720210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720218 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5720218 : Nat := 118140960795 + 5720218 * 2 ^ 59
def prefixEnd_5720218 : Nat := 4983230072969 + 3 ^ 40 * 5720218 * 2
def baseEnd_5720218 : Nat := 2937221282500405854468203

theorem tailTrace_5720218 : CollatzResearch.WordTrace tailWord_5720218 prefixEnd_5720218 2937221282500405854468203 := by
  unfold tailWord_5720218
  simp only [CollatzResearch.WordTrace]
  refine ⟨52158372597658649075426327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139088993593756397534470205 52158372597658649075426327)
  ·
    refine ⟨78237558896487973613139491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52158372597658649075426327 78237558896487973613139491)
    ·
      refine ⟨117356338344731960419709237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78237558896487973613139491 117356338344731960419709237)
      ·
        refine ⟨11002156719818621289347741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117356338344731960419709237 11002156719818621289347741)
        ·
          refine ⟨4125808769931982983505403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11002156719818621289347741 4125808769931982983505403)
          ·
            refine ⟨6188713154897974475258105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125808769931982983505403 6188713154897974475258105)
            ·
              refine ⟨4641534866173480856443579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188713154897974475258105 4641534866173480856443579)
              ·
                refine ⟨6962302299260221284665369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641534866173480856443579 6962302299260221284665369)
                ·
                  refine ⟨5221726724445165963499027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962302299260221284665369 5221726724445165963499027)
                  ·
                    refine ⟨7832590086667748945248541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5221726724445165963499027 7832590086667748945248541)
                    ·
                      refine ⟨2937221282500405854468203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832590086667748945248541 2937221282500405854468203)
                      ·
                        rfl

theorem cell23_5720218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5720218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720218 prefixEnd_5720218 := by exact prefixLift 5720218
  have htrace : WordTrace (prefixWord ++ tailWord_5720218) baseStart_5720218 baseEnd_5720218 := by
    simpa [prefixWord, tailWord_5720218, baseEnd_5720218] using wordTrace_append hprefix tailTrace_5720218
  have hstable : (prefixWord ++ tailWord_5720218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720218).length < 2 ^ (prefixWord ++ tailWord_5720218).sum := by decide
  have hdescent : baseEnd_5720218 < baseStart_5720218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720224 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 2, 2, 2]
def baseStart_5720224 : Nat := 118140960795 + 5720224 * 2 ^ 59
def prefixEnd_5720224 : Nat := 4983230072969 + 3 ^ 40 * 5720224 * 2
def baseEnd_5720224 : Nat := 2937224363384332830993175

theorem tailTrace_5720224 : CollatzResearch.WordTrace tailWord_5720224 prefixEnd_5720224 2937224363384332830993175 := by
  unfold tailWord_5720224
  simp only [CollatzResearch.WordTrace]
  refine ⟨104316854614306429663211863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139089139485741906217615817 104316854614306429663211863)
  ·
    refine ⟨156475281921459644494817795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104316854614306429663211863 156475281921459644494817795)
    ·
      refine ⟨234712922882189466742226693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156475281921459644494817795 234712922882189466742226693)
      ·
        refine ⟨44008673040410525014167505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234712922882189466742226693 44008673040410525014167505)
        ·
          refine ⟨33006504780307893760625629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44008673040410525014167505 33006504780307893760625629)
          ·
            refine ⟨12377439292615460160234611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33006504780307893760625629 12377439292615460160234611)
            ·
              refine ⟨18566158938923190240351917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12377439292615460160234611 18566158938923190240351917)
              ·
                refine ⟨6962309602096196340131969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18566158938923190240351917 6962309602096196340131969)
                ·
                  refine ⟨5221732201572147255098977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962309602096196340131969 5221732201572147255098977)
                  ·
                    refine ⟨3916299151179110441324233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5221732201572147255098977 3916299151179110441324233)
                    ·
                      refine ⟨2937224363384332830993175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916299151179110441324233 2937224363384332830993175)
                      ·
                        rfl

theorem cell23_5720224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_5720224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720224 prefixEnd_5720224 := by exact prefixLift 5720224
  have htrace : WordTrace (prefixWord ++ tailWord_5720224) baseStart_5720224 baseEnd_5720224 := by
    simpa [prefixWord, tailWord_5720224, baseEnd_5720224] using wordTrace_append hprefix tailTrace_5720224
  have hstable : (prefixWord ++ tailWord_5720224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720224).length < 2 ^ (prefixWord ++ tailWord_5720224).sum := by decide
  have hdescent : baseEnd_5720224 < baseStart_5720224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720258 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_5720258 : Nat := 118140960795 + 5720258 * 2 ^ 59
def prefixEnd_5720258 : Nat := 4983230072969 + 3 ^ 40 * 5720258 * 2
def baseEnd_5720258 : Nat := 2937241821726585697968019

theorem tailTrace_5720258 : CollatzResearch.WordTrace tailWord_5720258 prefixEnd_5720258 2937241821726585697968019 := by
  unfold tailWord_5720258
  simp only [CollatzResearch.WordTrace]
  refine ⟨52158737327622420783290357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139089966206993122088774285 52158737327622420783290357)
  ·
    refine ⟨4889881624464601948433471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52158737327622420783290357 4889881624464601948433471)
    ·
      refine ⟨7334822436696902922650207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4889881624464601948433471 7334822436696902922650207)
      ·
        refine ⟨11002233655045354383975311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334822436696902922650207 11002233655045354383975311)
        ·
          refine ⟨16503350482568031575962967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11002233655045354383975311 16503350482568031575962967)
          ·
            refine ⟨24755025723852047363944451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16503350482568031575962967 24755025723852047363944451)
            ·
              refine ⟨37132538585778071045916677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24755025723852047363944451 37132538585778071045916677)
              ·
                refine ⟨6962350984833388321109377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37132538585778071045916677 6962350984833388321109377)
                ·
                  refine ⟨5221763238625041240832033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962350984833388321109377 5221763238625041240832033)
                  ·
                    refine ⟨3916322428968780930624025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5221763238625041240832033 3916322428968780930624025)
                    ·
                      refine ⟨2937241821726585697968019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916322428968780930624025 2937241821726585697968019)
                      ·
                        rfl

theorem cell23_5720258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_5720258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720258 prefixEnd_5720258 := by exact prefixLift 5720258
  have htrace : WordTrace (prefixWord ++ tailWord_5720258) baseStart_5720258 baseEnd_5720258 := by
    simpa [prefixWord, tailWord_5720258, baseEnd_5720258] using wordTrace_append hprefix tailTrace_5720258
  have hstable : (prefixWord ++ tailWord_5720258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720258).length < 2 ^ (prefixWord ++ tailWord_5720258).sum := by decide
  have hdescent : baseEnd_5720258 < baseStart_5720258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720263 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_5720263 : Nat := 118140960795 + 5720263 * 2 ^ 59
def prefixEnd_5720263 : Nat := 4983230072969 + 3 ^ 40 * 5720263 * 2
def baseEnd_5720263 : Nat := 2937244389129858178405495

theorem tailTrace_5720263 : CollatzResearch.WordTrace tailWord_5720263 prefixEnd_5720263 2937244389129858178405495 := by
  unfold tailWord_5720263
  simp only [CollatzResearch.WordTrace]
  refine ⟨208635131675471568987093443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139090087783647712658062295 208635131675471568987093443)
  ·
    refine ⟨312952697513207353480640165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208635131675471568987093443 312952697513207353480640165)
    ·
      refine ⟨58678630783726378777620031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312952697513207353480640165 58678630783726378777620031)
      ·
        refine ⟨88017946175589568166430047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58678630783726378777620031 88017946175589568166430047)
        ·
          refine ⟨132026919263384352249645071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88017946175589568166430047 132026919263384352249645071)
          ·
            refine ⟨198040378895076528374467607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132026919263384352249645071 198040378895076528374467607)
            ·
              refine ⟨297060568342614792561701411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198040378895076528374467607 297060568342614792561701411)
              ·
                refine ⟨445590852513922188842552117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297060568342614792561701411 445590852513922188842552117)
                ·
                  refine ⟨41774142423180205203989261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445590852513922188842552117 41774142423180205203989261)
                  ·
                    refine ⟨15665303408692576951495973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41774142423180205203989261 15665303408692576951495973)
                    ·
                      refine ⟨2937244389129858178405495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15665303408692576951495973 2937244389129858178405495)
                      ·
                        rfl

theorem cell23_5720263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_5720263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720263 prefixEnd_5720263 := by exact prefixLift 5720263
  have htrace : WordTrace (prefixWord ++ tailWord_5720263) baseStart_5720263 baseEnd_5720263 := by
    simpa [prefixWord, tailWord_5720263, baseEnd_5720263] using wordTrace_append hprefix tailTrace_5720263
  have hstable : (prefixWord ++ tailWord_5720263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720263).length < 2 ^ (prefixWord ++ tailWord_5720263).sum := by decide
  have hdescent : baseEnd_5720263 < baseStart_5720263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720270 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_5720270 : Nat := 118140960795 + 5720270 * 2 ^ 59
def prefixEnd_5720270 : Nat := 4983230072969 + 3 ^ 40 * 5720270 * 2
def baseEnd_5720270 : Nat := 2937247983494439651017963

theorem tailTrace_5720270 : CollatzResearch.WordTrace tailWord_5720270 prefixEnd_5720270 2937247983494439651017963 := by
  unfold tailWord_5720270
  simp only [CollatzResearch.WordTrace]
  refine ⟨26079423373305776147824783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139090257990964139455065509 26079423373305776147824783)
  ·
    refine ⟨39119135059958664221737175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26079423373305776147824783 39119135059958664221737175)
    ·
      refine ⟨58678702589937996332605763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39119135059958664221737175 58678702589937996332605763)
      ·
        refine ⟨88018053884906994498908645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58678702589937996332605763 88018053884906994498908645)
        ·
          refine ⟨16503385103420061468545371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88018053884906994498908645 16503385103420061468545371)
          ·
            refine ⟨24755077655130092202818057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16503385103420061468545371 24755077655130092202818057)
            ·
              refine ⟨18566308241347569152113543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24755077655130092202818057 18566308241347569152113543)
              ·
                refine ⟨27849462362021353728170315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18566308241347569152113543 27849462362021353728170315)
                ·
                  refine ⟨41774193543032030592255473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27849462362021353728170315 41774193543032030592255473)
                  ·
                    refine ⟨31330645157274022944191605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41774193543032030592255473 31330645157274022944191605)
                    ·
                      refine ⟨2937247983494439651017963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31330645157274022944191605 2937247983494439651017963)
                      ·
                        rfl

theorem cell23_5720270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_5720270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720270 prefixEnd_5720270 := by exact prefixLift 5720270
  have htrace : WordTrace (prefixWord ++ tailWord_5720270) baseStart_5720270 baseEnd_5720270 := by
    simpa [prefixWord, tailWord_5720270, baseEnd_5720270] using wordTrace_append hprefix tailTrace_5720270
  have hstable : (prefixWord ++ tailWord_5720270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720270).length < 2 ^ (prefixWord ++ tailWord_5720270).sum := by decide
  have hdescent : baseEnd_5720270 < baseStart_5720270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720300 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_5720300 : Nat := 118140960795 + 5720300 * 2 ^ 59
def prefixEnd_5720300 : Nat := 4983230072969 + 3 ^ 40 * 5720300 * 2
def baseEnd_5720300 : Nat := 2937263387914074533642825

theorem tailTrace_5720300 : CollatzResearch.WordTrace tailWord_5720300 prefixEnd_5720300 2937263387914074533642825 := by
  unfold tailWord_5720300
  simp only [CollatzResearch.WordTrace]
  refine ⟨104318240588168762153095177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139090987450891682870793569 104318240588168762153095177)
  ·
    refine ⟨78238680441126571614821383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104318240588168762153095177 78238680441126571614821383)
    ·
      refine ⟨117358020661689857422232075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78238680441126571614821383 117358020661689857422232075)
      ·
        refine ⟨176037030992534786133348113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117358020661689857422232075 176037030992534786133348113)
        ·
          refine ⟨132027773244401089600011085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176037030992534786133348113 132027773244401089600011085)
          ·
            refine ⟨49510414966650408600004157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132027773244401089600011085 49510414966650408600004157)
            ·
              refine ⟨18566405612493903225001559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49510414966650408600004157 18566405612493903225001559)
              ·
                refine ⟨27849608418740854837502339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18566405612493903225001559 27849608418740854837502339)
                ·
                  refine ⟨41774412628111282256253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27849608418740854837502339 41774412628111282256253509)
                  ·
                    refine ⟨7832702367770865423047533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41774412628111282256253509 7832702367770865423047533)
                    ·
                      refine ⟨2937263387914074533642825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832702367770865423047533 2937263387914074533642825)
                      ·
                        rfl

theorem cell23_5720300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_5720300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720300 prefixEnd_5720300 := by exact prefixLift 5720300
  have htrace : WordTrace (prefixWord ++ tailWord_5720300) baseStart_5720300 baseEnd_5720300 := by
    simpa [prefixWord, tailWord_5720300, baseEnd_5720300] using wordTrace_append hprefix tailTrace_5720300
  have hstable : (prefixWord ++ tailWord_5720300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720300).length < 2 ^ (prefixWord ++ tailWord_5720300).sum := by decide
  have hdescent : baseEnd_5720300 < baseStart_5720300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720310 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5720310 : Nat := 118140960795 + 5720310 * 2 ^ 59
def prefixEnd_5720310 : Nat := 4983230072969 + 3 ^ 40 * 5720310 * 2
def baseEnd_5720310 : Nat := 2937268522720619494517779

theorem tailTrace_5720310 : CollatzResearch.WordTrace tailWord_5720310 prefixEnd_5720310 2937268522720619494517779 := by
  unfold tailWord_5720310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039802869143831000878399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139091230604200864009369589 13039802869143831000878399)
  ·
    refine ⟨19559704303715746501317599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13039802869143831000878399 19559704303715746501317599)
    ·
      refine ⟨29339556455573619751976399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19559704303715746501317599 29339556455573619751976399)
      ·
        refine ⟨44009334683360429627964599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29339556455573619751976399 44009334683360429627964599)
        ·
          refine ⟨66014002025040644441946899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44009334683360429627964599 66014002025040644441946899)
          ·
            refine ⟨99021003037560966662920349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66014002025040644441946899 99021003037560966662920349)
            ·
              refine ⟨37132876139085362498595131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99021003037560966662920349 37132876139085362498595131)
              ·
                refine ⟨55699314208628043747892697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37132876139085362498595131 55699314208628043747892697)
                ·
                  refine ⟨41774485656471032810919523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55699314208628043747892697 41774485656471032810919523)
                  ·
                    refine ⟨62661728484706549216379285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41774485656471032810919523 62661728484706549216379285)
                    ·
                      refine ⟨2937268522720619494517779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62661728484706549216379285 2937268522720619494517779)
                      ·
                        rfl

theorem cell23_5720310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5720310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720310 prefixEnd_5720310 := by exact prefixLift 5720310
  have htrace : WordTrace (prefixWord ++ tailWord_5720310) baseStart_5720310 baseEnd_5720310 := by
    simpa [prefixWord, tailWord_5720310, baseEnd_5720310] using wordTrace_append hprefix tailTrace_5720310
  have hstable : (prefixWord ++ tailWord_5720310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720310).length < 2 ^ (prefixWord ++ tailWord_5720310).sum := by decide
  have hdescent : baseEnd_5720310 < baseStart_5720310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720320 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 6]
def baseStart_5720320 : Nat := 118140960795 + 5720320 * 2 ^ 59
def prefixEnd_5720320 : Nat := 4983230072969 + 3 ^ 40 * 5720320 * 2
def baseEnd_5720320 : Nat := 326363739725240495043637

theorem tailTrace_5720320 : CollatzResearch.WordTrace tailWord_5720320 prefixEnd_5720320 326363739725240495043637 := by
  unfold tailWord_5720320
  simp only [CollatzResearch.WordTrace]
  refine ⟨104318605318132533860959207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139091473757510045147945609 104318605318132533860959207)
  ·
    refine ⟨156477907977198800791438811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104318605318132533860959207 156477907977198800791438811)
    ·
      refine ⟨234716861965798201187158217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156477907977198800791438811 234716861965798201187158217)
      ·
        refine ⟨176037646474348650890368663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234716861965798201187158217 176037646474348650890368663)
        ·
          refine ⟨264056469711522976335552995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176037646474348650890368663 264056469711522976335552995)
          ·
            refine ⟨396084704567284464503329493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264056469711522976335552995 396084704567284464503329493)
            ·
              refine ⟨9283235263295729636796785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 396084704567284464503329493 9283235263295729636796785)
              ·
                refine ⟨6962426447471797227597589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9283235263295729636796785 6962426447471797227597589)
                ·
                  refine ⟨326363739725240495043637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6962426447471797227597589 326363739725240495043637)
                  ·
                    rfl

theorem cell23_5720320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_5720320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720320 prefixEnd_5720320 := by exact prefixLift 5720320
  have htrace : WordTrace (prefixWord ++ tailWord_5720320) baseStart_5720320 baseEnd_5720320 := by
    simpa [prefixWord, tailWord_5720320, baseEnd_5720320] using wordTrace_append hprefix tailTrace_5720320
  have hstable : (prefixWord ++ tailWord_5720320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720320).length < 2 ^ (prefixWord ++ tailWord_5720320).sum := by decide
  have hdescent : baseEnd_5720320 < baseStart_5720320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720323 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_5720323 : Nat := 118140960795 + 5720323 * 2 ^ 59
def prefixEnd_5720323 : Nat := 4983230072969 + 3 ^ 40 * 5720323 * 2
def baseEnd_5720323 : Nat := 2937275197969127943655219

theorem tailTrace_5720323 : CollatzResearch.WordTrace tailWord_5720323 prefixEnd_5720323 2937275197969127943655219 := by
  unfold tailWord_5720323
  simp only [CollatzResearch.WordTrace]
  refine ⟨208637320055254199234277623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139091546703502799489518415 208637320055254199234277623)
  ·
    refine ⟨312955980082881298851416435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208637320055254199234277623 312955980082881298851416435)
    ·
      refine ⟨469433970124321948277124653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312955980082881298851416435 469433970124321948277124653)
      ·
        refine ⟨176037738796620730603921745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469433970124321948277124653 176037738796620730603921745)
        ·
          refine ⟨132028304097465547952941309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176037738796620730603921745 132028304097465547952941309)
          ·
            refine ⟨49510614036549580482352991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132028304097465547952941309 49510614036549580482352991)
            ·
              refine ⟨74265921054824370723529487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49510614036549580482352991 74265921054824370723529487)
              ·
                refine ⟨111398881582236556085294231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74265921054824370723529487 111398881582236556085294231)
                ·
                  refine ⟨167098322373354834127941347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111398881582236556085294231 167098322373354834127941347)
                  ·
                    refine ⟨250647483560032251191912021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167098322373354834127941347 250647483560032251191912021)
                    ·
                      refine ⟨2937275197969127943655219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250647483560032251191912021 2937275197969127943655219)
                      ·
                        rfl

theorem cell23_5720323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_5720323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720323 prefixEnd_5720323 := by exact prefixLift 5720323
  have htrace : WordTrace (prefixWord ++ tailWord_5720323) baseStart_5720323 baseEnd_5720323 := by
    simpa [prefixWord, tailWord_5720323, baseEnd_5720323] using wordTrace_append hprefix tailTrace_5720323
  have hstable : (prefixWord ++ tailWord_5720323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720323).length < 2 ^ (prefixWord ++ tailWord_5720323).sum := by decide
  have hdescent : baseEnd_5720323 < baseStart_5720323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720324 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5720324 : Nat := 118140960795 + 5720324 * 2 ^ 59
def prefixEnd_5720324 : Nat := 4983230072969 + 3 ^ 40 * 5720324 * 2
def baseEnd_5720324 : Nat := 979091903816594146580905

theorem tailTrace_5720324 : CollatzResearch.WordTrace tailWord_5720324 prefixEnd_5720324 979091903816594146580905 := by
  unfold tailWord_5720324
  simp only [CollatzResearch.WordTrace]
  refine ⟨104318678264125288202532013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139091571018833717603376017 104318678264125288202532013)
  ·
    refine ⟨39119504349046983075949505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104318678264125288202532013 39119504349046983075949505)
    ·
      refine ⟨29339628261785237306962129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39119504349046983075949505 29339628261785237306962129)
      ·
        refine ⟨22004721196338927980221597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29339628261785237306962129 22004721196338927980221597)
        ·
          refine ⟨8251770448627097992583099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22004721196338927980221597 8251770448627097992583099)
          ·
            refine ⟨12377655672940646988874649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251770448627097992583099 12377655672940646988874649)
            ·
              refine ⟨9283241754705485241655987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12377655672940646988874649 9283241754705485241655987)
              ·
                refine ⟨13924862632058227862483981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9283241754705485241655987 13924862632058227862483981)
                ·
                  refine ⟨5221823487021835448431493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13924862632058227862483981 5221823487021835448431493)
                  ·
                    refine ⟨979091903816594146580905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5221823487021835448431493 979091903816594146580905)
                    ·
                      rfl

theorem cell23_5720324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5720324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720324 prefixEnd_5720324 := by exact prefixLift 5720324
  have htrace : WordTrace (prefixWord ++ tailWord_5720324) baseStart_5720324 baseEnd_5720324 := by
    simpa [prefixWord, tailWord_5720324, baseEnd_5720324] using wordTrace_append hprefix tailTrace_5720324
  have hstable : (prefixWord ++ tailWord_5720324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720324).length < 2 ^ (prefixWord ++ tailWord_5720324).sum := by decide
  have hdescent : baseEnd_5720324 < baseStart_5720324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720337 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 6]
def baseStart_5720337 : Nat := 118140960795 + 5720337 * 2 ^ 59
def prefixEnd_5720337 : Nat := 4983230072969 + 3 ^ 40 * 5720337 * 2
def baseEnd_5720337 : Nat := 326364709633143432097795

theorem tailTrace_5720337 : CollatzResearch.WordTrace tailWord_5720337 prefixEnd_5720337 326364709633143432097795 := by
  unfold tailWord_5720337
  simp only [CollatzResearch.WordTrace]
  refine ⟨208637830677203479625287265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139091887118135653083524843 208637830677203479625287265)
  ·
    refine ⟨156478373007902609718965449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208637830677203479625287265 156478373007902609718965449)
    ·
      refine ⟨117358779755926957289224087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156478373007902609718965449 117358779755926957289224087)
      ·
        refine ⟨176038169633890435933836131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117358779755926957289224087 176038169633890435933836131)
        ·
          refine ⟨264057254450835653900754197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176038169633890435933836131 264057254450835653900754197)
          ·
            refine ⟨12377683802382921276597853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 264057254450835653900754197 12377683802382921276597853)
            ·
              refine ⟨4641631425893595478724195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12377683802382921276597853 4641631425893595478724195)
              ·
                refine ⟨6962447138840393218086293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641631425893595478724195 6962447138840393218086293)
                ·
                  refine ⟨326364709633143432097795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6962447138840393218086293 326364709633143432097795)
                  ·
                    rfl

theorem cell23_5720337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 6].length) (baseStart_5720337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720337 prefixEnd_5720337 := by exact prefixLift 5720337
  have htrace : WordTrace (prefixWord ++ tailWord_5720337) baseStart_5720337 baseEnd_5720337 := by
    simpa [prefixWord, tailWord_5720337, baseEnd_5720337] using wordTrace_append hprefix tailTrace_5720337
  have hstable : (prefixWord ++ tailWord_5720337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720337).length < 2 ^ (prefixWord ++ tailWord_5720337).sum := by decide
  have hdescent : baseEnd_5720337 < baseStart_5720337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720347 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 3]
def baseStart_5720347 : Nat := 118140960795 + 5720347 * 2 ^ 59
def prefixEnd_5720347 : Nat := 4983230072969 + 3 ^ 40 * 5720347 * 2
def baseEnd_5720347 : Nat := 2937287521504835849755109

theorem tailTrace_5720347 : CollatzResearch.WordTrace tailWord_5720347 prefixEnd_5720347 2937287521504835849755109 := by
  unfold tailWord_5720347
  simp only [CollatzResearch.WordTrace]
  refine ⟨208638195407167251333151295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139092130271444834222100863 208638195407167251333151295)
  ·
    refine ⟨312957293110750876999726943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208638195407167251333151295 312957293110750876999726943)
    ·
      refine ⟨469435939666126315499590415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312957293110750876999726943 469435939666126315499590415)
      ·
        refine ⟨704153909499189473249385623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469435939666126315499590415 704153909499189473249385623)
        ·
          refine ⟨1056230864248784209874078435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704153909499189473249385623 1056230864248784209874078435)
          ·
            refine ⟨1584346296373176314811117653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056230864248784209874078435 1584346296373176314811117653)
            ·
              refine ⟨18566558160623159939192785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1584346296373176314811117653 18566558160623159939192785)
              ·
                refine ⟨13924918620467369954394589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18566558160623159939192785 13924918620467369954394589)
                ·
                  refine ⟨5221844482675263732897971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13924918620467369954394589 5221844482675263732897971)
                  ·
                    refine ⟨7832766724012895599346957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5221844482675263732897971 7832766724012895599346957)
                    ·
                      refine ⟨2937287521504835849755109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832766724012895599346957 2937287521504835849755109)
                      ·
                        rfl

theorem cell23_5720347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 3].length) (baseStart_5720347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720347 prefixEnd_5720347 := by exact prefixLift 5720347
  have htrace : WordTrace (prefixWord ++ tailWord_5720347) baseStart_5720347 baseEnd_5720347 := by
    simpa [prefixWord, tailWord_5720347, baseEnd_5720347] using wordTrace_append hprefix tailTrace_5720347
  have hstable : (prefixWord ++ tailWord_5720347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720347).length < 2 ^ (prefixWord ++ tailWord_5720347).sum := by decide
  have hdescent : baseEnd_5720347 < baseStart_5720347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720388 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 6]
def baseStart_5720388 : Nat := 118140960795 + 5720388 * 2 ^ 59
def prefixEnd_5720388 : Nat := 4983230072969 + 3 ^ 40 * 5720388 * 2
def baseEnd_5720388 : Nat := 326367619356852243260269

theorem tailTrace_5720388 : CollatzResearch.WordTrace tailWord_5720388 prefixEnd_5720388 326367619356852243260269 := by
  unfold tailWord_5720388
  simp only [CollatzResearch.WordTrace]
  refine ⟨104319845400009357667696909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139093127200012476890262545 104319845400009357667696909)
  ·
    refine ⟨39119942025003509125386341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104319845400009357667696909 39119942025003509125386341)
    ·
      refine ⟨7334989129688157961009939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39119942025003509125386341 7334989129688157961009939)
      ·
        refine ⟨11002483694532236941514909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334989129688157961009939 11002483694532236941514909)
        ·
          refine ⟨4125931385449588853068091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11002483694532236941514909 4125931385449588853068091)
          ·
            refine ⟨6188897078174383279602137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125931385449588853068091 6188897078174383279602137)
            ·
              refine ⟨4641672808630787459701603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188897078174383279602137 4641672808630787459701603)
              ·
                refine ⟨6962509212946181189552405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641672808630787459701603 6962509212946181189552405)
                ·
                  refine ⟨326367619356852243260269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6962509212946181189552405 326367619356852243260269)
                  ·
                    rfl

theorem cell23_5720388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_5720388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720388 prefixEnd_5720388 := by exact prefixLift 5720388
  have htrace : WordTrace (prefixWord ++ tailWord_5720388) baseStart_5720388 baseEnd_5720388 := by
    simpa [prefixWord, tailWord_5720388, baseEnd_5720388] using wordTrace_append hprefix tailTrace_5720388
  have hstable : (prefixWord ++ tailWord_5720388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720388).length < 2 ^ (prefixWord ++ tailWord_5720388).sum := by decide
  have hdescent : baseEnd_5720388 < baseStart_5720388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720400 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_5720400 : Nat := 118140960795 + 5720400 * 2 ^ 59
def prefixEnd_5720400 : Nat := 4983230072969 + 3 ^ 40 * 5720400 * 2
def baseEnd_5720400 : Nat := 2937314735979524142392365

theorem tailTrace_5720400 : CollatzResearch.WordTrace tailWord_5720400 prefixEnd_5720400 2937314735979524142392365 := by
  unfold tailWord_5720400
  simp only [CollatzResearch.WordTrace]
  refine ⟨104320064237987620692415327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139093418983983494256553769 104320064237987620692415327)
  ·
    refine ⟨156480096356981431038622991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104320064237987620692415327 156480096356981431038622991)
    ·
      refine ⟨234720144535472146557934487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156480096356981431038622991 234720144535472146557934487)
      ·
        refine ⟨352080216803208219836901731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234720144535472146557934487 352080216803208219836901731)
        ·
          refine ⟨528120325204812329755352597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352080216803208219836901731 528120325204812329755352597)
          ·
            refine ⟨24755640243975577957282153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 528120325204812329755352597 24755640243975577957282153)
            ·
              refine ⟨18566730182981683467961615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24755640243975577957282153 18566730182981683467961615)
              ·
                refine ⟨27850095274472525201942423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18566730182981683467961615 27850095274472525201942423)
                ·
                  refine ⟨41775142911708787802913635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27850095274472525201942423 41775142911708787802913635)
                  ·
                    refine ⟨62662714367563181704370453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41775142911708787802913635 62662714367563181704370453)
                    ·
                      refine ⟨2937314735979524142392365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62662714367563181704370453 2937314735979524142392365)
                      ·
                        rfl

theorem cell23_5720400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_5720400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720400 prefixEnd_5720400 := by exact prefixLift 5720400
  have htrace : WordTrace (prefixWord ++ tailWord_5720400) baseStart_5720400 baseEnd_5720400 := by
    simpa [prefixWord, tailWord_5720400, baseEnd_5720400] using wordTrace_append hprefix tailTrace_5720400
  have hstable : (prefixWord ++ tailWord_5720400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720400).length < 2 ^ (prefixWord ++ tailWord_5720400).sum := by decide
  have hdescent : baseEnd_5720400 < baseStart_5720400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720404 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_5720404 : Nat := 118140960795 + 5720404 * 2 ^ 59
def prefixEnd_5720404 : Nat := 4983230072969 + 3 ^ 40 * 5720404 * 2
def baseEnd_5720404 : Nat := 2937316789902142126742347

theorem tailTrace_5720404 : CollatzResearch.WordTrace tailWord_5720404 prefixEnd_5720404 2937316789902142126742347 := by
  unfold tailWord_5720404
  simp only [CollatzResearch.WordTrace]
  refine ⟨104320137183980375033988133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139093516245307166711984177 104320137183980375033988133)
  ·
    refine ⟨19560025721996320318872775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104320137183980375033988133 19560025721996320318872775)
    ·
      refine ⟨29340038582994480478309163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19560025721996320318872775 29340038582994480478309163)
      ·
        refine ⟨44010057874491720717463745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29340038582994480478309163 44010057874491720717463745)
        ·
          refine ⟨33007543405868790538097809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44010057874491720717463745 33007543405868790538097809)
          ·
            refine ⟨24755657554401592903573357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33007543405868790538097809 24755657554401592903573357)
            ·
              refine ⟨9283371582900597338840009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24755657554401592903573357 9283371582900597338840009)
              ·
                refine ⟨6962528687175448004130007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9283371582900597338840009 6962528687175448004130007)
                ·
                  refine ⟨10443793030763172006195011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962528687175448004130007 10443793030763172006195011)
                  ·
                    refine ⟨15665689546144758009292517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10443793030763172006195011 15665689546144758009292517)
                    ·
                      refine ⟨2937316789902142126742347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15665689546144758009292517 2937316789902142126742347)
                      ·
                        rfl

theorem cell23_5720404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_5720404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720404 prefixEnd_5720404 := by exact prefixLift 5720404
  have htrace : WordTrace (prefixWord ++ tailWord_5720404) baseStart_5720404 baseEnd_5720404 := by
    simpa [prefixWord, tailWord_5720404, baseEnd_5720404] using wordTrace_append hprefix tailTrace_5720404
  have hstable : (prefixWord ++ tailWord_5720404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720404).length < 2 ^ (prefixWord ++ tailWord_5720404).sum := by decide
  have hdescent : baseEnd_5720404 < baseStart_5720404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720407 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_5720407 : Nat := 118140960795 + 5720407 * 2 ^ 59
def prefixEnd_5720407 : Nat := 4983230072969 + 3 ^ 40 * 5720407 * 2
def baseEnd_5720407 : Nat := 2937318330344105615004833

theorem tailTrace_5720407 : CollatzResearch.WordTrace tailWord_5720407 prefixEnd_5720407 2937318330344105615004833 := by
  unfold tailWord_5720407
  simp only [CollatzResearch.WordTrace]
  refine ⟨208640383786949881580335475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139093589191299921053556983 208640383786949881580335475)
  ·
    refine ⟨312960575680424822370503213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208640383786949881580335475 312960575680424822370503213)
    ·
      refine ⟨117360215880159308388938705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312960575680424822370503213 117360215880159308388938705)
      ·
        refine ⟨88020161910119481291704029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117360215880159308388938705 88020161910119481291704029)
        ·
          refine ⟨33007560716294805484389011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88020161910119481291704029 33007560716294805484389011)
          ·
            refine ⟨49511341074442208226583517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33007560716294805484389011 49511341074442208226583517)
            ·
              refine ⟨18566752902915828084968819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49511341074442208226583517 18566752902915828084968819)
              ·
                refine ⟨27850129354373742127453229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18566752902915828084968819 27850129354373742127453229)
                ·
                  refine ⟨10443798507890153297794961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27850129354373742127453229 10443798507890153297794961)
                  ·
                    refine ⟨7832848880917614973346221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10443798507890153297794961 7832848880917614973346221)
                    ·
                      refine ⟨2937318330344105615004833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832848880917614973346221 2937318330344105615004833)
                      ·
                        rfl

theorem cell23_5720407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_5720407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720407 prefixEnd_5720407 := by exact prefixLift 5720407
  have htrace : WordTrace (prefixWord ++ tailWord_5720407) baseStart_5720407 baseEnd_5720407 := by
    simpa [prefixWord, tailWord_5720407, baseEnd_5720407] using wordTrace_append hprefix tailTrace_5720407
  have hstable : (prefixWord ++ tailWord_5720407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720407).length < 2 ^ (prefixWord ++ tailWord_5720407).sum := by decide
  have hdescent : baseEnd_5720407 < baseStart_5720407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720424 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5720424 : Nat := 118140960795 + 5720424 * 2 ^ 59
def prefixEnd_5720424 : Nat := 4983230072969 + 3 ^ 40 * 5720424 * 2
def baseEnd_5720424 : Nat := 2937327059515232048492255

theorem tailTrace_5720424 : CollatzResearch.WordTrace tailWord_5720424 prefixEnd_5720424 2937327059515232048492255 := by
  unfold tailWord_5720424
  simp only [CollatzResearch.WordTrace]
  refine ⟨104320501913944146741852163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139094002551925528989136217 104320501913944146741852163)
  ·
    refine ⟨156480752870916220112778245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104320501913944146741852163 156480752870916220112778245)
    ·
      refine ⟨29340141163296791271145921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156480752870916220112778245 29340141163296791271145921)
      ·
        refine ⟨22005105872472593453359441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29340141163296791271145921 22005105872472593453359441)
        ·
          refine ⟨16503829404354445090019581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22005105872472593453359441 16503829404354445090019581)
          ·
            refine ⟨6188936026632916908757343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16503829404354445090019581 6188936026632916908757343)
            ·
              refine ⟨9283404039949375363136015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188936026632916908757343 9283404039949375363136015)
              ·
                refine ⟨13925106059924063044704023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9283404039949375363136015 13925106059924063044704023)
                ·
                  refine ⟨20887659089886094567056035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13925106059924063044704023 20887659089886094567056035)
                  ·
                    refine ⟨31331488634829141850584053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20887659089886094567056035 31331488634829141850584053)
                    ·
                      refine ⟨2937327059515232048492255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31331488634829141850584053 2937327059515232048492255)
                      ·
                        rfl

theorem cell23_5720424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5720424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720424 prefixEnd_5720424 := by exact prefixLift 5720424
  have htrace : WordTrace (prefixWord ++ tailWord_5720424) baseStart_5720424 baseEnd_5720424 := by
    simpa [prefixWord, tailWord_5720424, baseEnd_5720424] using wordTrace_append hprefix tailTrace_5720424
  have hstable : (prefixWord ++ tailWord_5720424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720424).length < 2 ^ (prefixWord ++ tailWord_5720424).sum := by decide
  have hdescent : baseEnd_5720424 < baseStart_5720424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720487 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5720487 : Nat := 118140960795 + 5720487 * 2 ^ 59
def prefixEnd_5720487 : Nat := 4983230072969 + 3 ^ 40 * 5720487 * 2
def baseEnd_5720487 : Nat := 979119802932155100668155

theorem tailTrace_5720487 : CollatzResearch.WordTrace tailWord_5720487 prefixEnd_5720487 979119802932155100668155 := by
  unfold tailWord_5720487
  simp only [CollatzResearch.WordTrace]
  refine ⟨208643301626660055243247715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139095534417773370162165143 208643301626660055243247715)
  ·
    refine ⟨312964952439990082864871573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208643301626660055243247715 312964952439990082864871573)
    ·
      refine ⟨14670232145624535134290855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 312964952439990082864871573 14670232145624535134290855)
      ·
        refine ⟨22005348218436802701436283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14670232145624535134290855 22005348218436802701436283)
        ·
          refine ⟨33008022327655204052154425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22005348218436802701436283 33008022327655204052154425)
          ·
            refine ⟨24756016745741403039115819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33008022327655204052154425 24756016745741403039115819)
            ·
              refine ⟨37134025118612104558673729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24756016745741403039115819 37134025118612104558673729)
              ·
                refine ⟨27850518838959078419005297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37134025118612104558673729 27850518838959078419005297)
                ·
                  refine ⟨20887889129219308814253973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27850518838959078419005297 20887889129219308814253973)
                  ·
                    refine ⟨979119802932155100668155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20887889129219308814253973 979119802932155100668155)
                    ·
                      rfl

theorem cell23_5720487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5720487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720487 prefixEnd_5720487 := by exact prefixLift 5720487
  have htrace : WordTrace (prefixWord ++ tailWord_5720487) baseStart_5720487 baseEnd_5720487 := by
    simpa [prefixWord, tailWord_5720487, baseEnd_5720487] using wordTrace_append hprefix tailTrace_5720487
  have hstable : (prefixWord ++ tailWord_5720487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720487).length < 2 ^ (prefixWord ++ tailWord_5720487).sum := by decide
  have hdescent : baseEnd_5720487 < baseStart_5720487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720488 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5720488 : Nat := 118140960795 + 5720488 * 2 ^ 59
def prefixEnd_5720488 : Nat := 4983230072969 + 3 ^ 40 * 5720488 * 2
def baseEnd_5720488 : Nat := 2937359922277119798091961

theorem tailTrace_5720488 : CollatzResearch.WordTrace tailWord_5720488 prefixEnd_5720488 2937359922277119798091961 := by
  unfold tailWord_5720488
  simp only [CollatzResearch.WordTrace]
  refine ⟨104321669049828216207017059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139095558733104288276022745 104321669049828216207017059)
  ·
    refine ⟨156482503574742324310525589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104321669049828216207017059 156482503574742324310525589)
    ·
      refine ⟨7335117355066046452055887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156482503574742324310525589 7335117355066046452055887)
      ·
        refine ⟨11002676032599069678083831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7335117355066046452055887 11002676032599069678083831)
        ·
          refine ⟨16504014048898604517125747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11002676032599069678083831 16504014048898604517125747)
          ·
            refine ⟨24756021073347906775688621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16504014048898604517125747 24756021073347906775688621)
            ·
              refine ⟨9283507902505465040883233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24756021073347906775688621 9283507902505465040883233)
              ·
                refine ⟨6962630926879098780662425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9283507902505465040883233 6962630926879098780662425)
                ·
                  refine ⟨5221973195159324085496819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962630926879098780662425 5221973195159324085496819)
                  ·
                    refine ⟨7832959792738986128245229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5221973195159324085496819 7832959792738986128245229)
                    ·
                      refine ⟨2937359922277119798091961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7832959792738986128245229 2937359922277119798091961)
                      ·
                        rfl

theorem cell23_5720488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5720488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720488 prefixEnd_5720488 := by exact prefixLift 5720488
  have htrace : WordTrace (prefixWord ++ tailWord_5720488) baseStart_5720488 baseEnd_5720488 := by
    simpa [prefixWord, tailWord_5720488, baseEnd_5720488] using wordTrace_append hprefix tailTrace_5720488
  have hstable : (prefixWord ++ tailWord_5720488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720488).length < 2 ^ (prefixWord ++ tailWord_5720488).sum := by decide
  have hdescent : baseEnd_5720488 < baseStart_5720488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720551 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 5]
def baseStart_5720551 : Nat := 118140960795 + 5720551 * 2 ^ 59
def prefixEnd_5720551 : Nat := 4983230072969 + 3 ^ 40 * 5720551 * 2
def baseEnd_5720551 : Nat := 326376919062039227956019

theorem tailTrace_5720551 : CollatzResearch.WordTrace tailWord_5720551 prefixEnd_5720551 326376919062039227956019 := by
  unfold tailWord_5720551
  simp only [CollatzResearch.WordTrace]
  refine ⟨208645635898428194173577507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139097090598952129449051671 208645635898428194173577507)
  ·
    refine ⟨312968453847642291260366261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208645635898428194173577507 312968453847642291260366261)
    ·
      refine ⟨29340792548216464805659337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312968453847642291260366261 29340792548216464805659337)
      ·
        refine ⟨22005594411162348604244503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29340792548216464805659337 22005594411162348604244503)
        ·
          refine ⟨33008391616743522906366755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22005594411162348604244503 33008391616743522906366755)
          ·
            refine ⟨49512587425115284359550133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33008391616743522906366755 49512587425115284359550133)
            ·
              refine ⟨4641805071104557908707825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49512587425115284359550133 4641805071104557908707825)
              ·
                refine ⟨3481353803328418431530869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641805071104557908707825 3481353803328418431530869)
                ·
                  refine ⟨326376919062039227956019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481353803328418431530869 326376919062039227956019)
                  ·
                    rfl

theorem cell23_5720551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 5].length) (baseStart_5720551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720551 prefixEnd_5720551 := by exact prefixLift 5720551
  have htrace : WordTrace (prefixWord ++ tailWord_5720551) baseStart_5720551 baseEnd_5720551 := by
    simpa [prefixWord, tailWord_5720551, baseEnd_5720551] using wordTrace_append hprefix tailTrace_5720551
  have hstable : (prefixWord ++ tailWord_5720551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720551).length < 2 ^ (prefixWord ++ tailWord_5720551).sum := by decide
  have hdescent : baseEnd_5720551 < baseStart_5720551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720562 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5720562 : Nat := 118140960795 + 5720562 * 2 ^ 59
def prefixEnd_5720562 : Nat := 4983230072969 + 3 ^ 40 * 5720562 * 2
def baseEnd_5720562 : Nat := 2937397919845552508566621

theorem tailTrace_5720562 : CollatzResearch.WordTrace tailWord_5720562 prefixEnd_5720562 2937397919845552508566621 := by
  unfold tailWord_5720562
  simp only [CollatzResearch.WordTrace]
  refine ⟨52161509275347085763056985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139097358067592228701485293 52161509275347085763056985)
  ·
    refine ⟨39121131956510314322292739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52161509275347085763056985 39121131956510314322292739)
    ·
      refine ⟨58681697934765471483439109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39121131956510314322292739 58681697934765471483439109)
      ·
        refine ⟨11002818362768525903144833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58681697934765471483439109 11002818362768525903144833)
        ·
          refine ⟨8252113772076394427358625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11002818362768525903144833 8252113772076394427358625)
          ·
            refine ⟨6189085329057295820518969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8252113772076394427358625 6189085329057295820518969)
            ·
              refine ⟨4641813996792971865389227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6189085329057295820518969 4641813996792971865389227)
              ·
                refine ⟨6962720995189457798083841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4641813996792971865389227 6962720995189457798083841)
                ·
                  refine ⟨5222040746392093348562881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6962720995189457798083841 5222040746392093348562881)
                  ·
                    refine ⟨3916530559794070011422161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5222040746392093348562881 3916530559794070011422161)
                    ·
                      refine ⟨2937397919845552508566621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916530559794070011422161 2937397919845552508566621)
                      ·
                        rfl

theorem cell23_5720562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5720562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720562 prefixEnd_5720562 := by exact prefixLift 5720562
  have htrace : WordTrace (prefixWord ++ tailWord_5720562) baseStart_5720562 baseEnd_5720562 := by
    simpa [prefixWord, tailWord_5720562, baseEnd_5720562] using wordTrace_append hprefix tailTrace_5720562
  have hstable : (prefixWord ++ tailWord_5720562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720562).length < 2 ^ (prefixWord ++ tailWord_5720562).sum := by decide
  have hdescent : baseEnd_5720562 < baseStart_5720562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720584 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_5720584 : Nat := 118140960795 + 5720584 * 2 ^ 59
def prefixEnd_5720584 : Nat := 4983230072969 + 3 ^ 40 * 5720584 * 2
def baseEnd_5720584 : Nat := 2937409216419951422491519

theorem tailTrace_5720584 : CollatzResearch.WordTrace tailWord_5720584 prefixEnd_5720584 2937409216419951422491519 := by
  unfold tailWord_5720584
  simp only [CollatzResearch.WordTrace]
  refine ⟨104323419753654320404764403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139097893004872427206352537 104323419753654320404764403)
  ·
    refine ⟨156485129630481480607146605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104323419753654320404764403 156485129630481480607146605)
    ·
      refine ⟨58681923611430555227679977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156485129630481480607146605 58681923611430555227679977)
      ·
        refine ⟨44011442708572916420759983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58681923611430555227679977 44011442708572916420759983)
        ·
          refine ⟨66017164062859374631139975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44011442708572916420759983 66017164062859374631139975)
          ·
            refine ⟨99025746094289061946709963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66017164062859374631139975 99025746094289061946709963)
            ·
              refine ⟨148538619141433592920064945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99025746094289061946709963 148538619141433592920064945)
              ·
                refine ⟨111403964356075194690048709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148538619141433592920064945 111403964356075194690048709)
                ·
                  refine ⟨20888243316764099004384133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111403964356075194690048709 20888243316764099004384133)
                  ·
                    refine ⟨3916545621893268563322025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20888243316764099004384133 3916545621893268563322025)
                    ·
                      refine ⟨2937409216419951422491519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916545621893268563322025 2937409216419951422491519)
                      ·
                        rfl

theorem cell23_5720584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_5720584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720584 prefixEnd_5720584 := by exact prefixLift 5720584
  have htrace : WordTrace (prefixWord ++ tailWord_5720584) baseStart_5720584 baseEnd_5720584 := by
    simpa [prefixWord, tailWord_5720584, baseEnd_5720584] using wordTrace_append hprefix tailTrace_5720584
  have hstable : (prefixWord ++ tailWord_5720584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720584).length < 2 ^ (prefixWord ++ tailWord_5720584).sum := by decide
  have hdescent : baseEnd_5720584 < baseStart_5720584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720597 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_5720597 : Nat := 118140960795 + 5720597 * 2 ^ 59
def prefixEnd_5720597 : Nat := 4983230072969 + 3 ^ 40 * 5720597 * 2
def baseEnd_5720597 : Nat := 2937415891668459871628959

theorem tailTrace_5720597 : CollatzResearch.WordTrace tailWord_5720597 prefixEnd_5720597 2937415891668459871628959 := by
  unfold tailWord_5720597
  simp only [CollatzResearch.WordTrace]
  refine ⟨208647313656261544029752045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139098209104174362686501363 208647313656261544029752045)
  ·
    refine ⟨78242742621098079011157017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208647313656261544029752045 78242742621098079011157017)
    ·
      refine ⟨58682056965823559258367763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78242742621098079011157017 58682056965823559258367763)
      ·
        refine ⟨88023085448735338887551645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58682056965823559258367763 88023085448735338887551645)
        ·
          refine ⟨33008657043275752082831867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88023085448735338887551645 33008657043275752082831867)
          ·
            refine ⟨49512985564913628124247801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33008657043275752082831867 49512985564913628124247801)
            ·
              refine ⟨37134739173685221093185851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49512985564913628124247801 37134739173685221093185851)
              ·
                refine ⟨55702108760527831639778777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37134739173685221093185851 55702108760527831639778777)
                ·
                  refine ⟨41776581570395873729834083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55702108760527831639778777 41776581570395873729834083)
                  ·
                    refine ⟨62664872355593810594751125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41776581570395873729834083 62664872355593810594751125)
                    ·
                      refine ⟨2937415891668459871628959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62664872355593810594751125 2937415891668459871628959)
                      ·
                        rfl

theorem cell23_5720597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_5720597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720597 prefixEnd_5720597 := by exact prefixLift 5720597
  have htrace : WordTrace (prefixWord ++ tailWord_5720597) baseStart_5720597 baseEnd_5720597 := by
    simpa [prefixWord, tailWord_5720597, baseEnd_5720597] using wordTrace_append hprefix tailTrace_5720597
  have hstable : (prefixWord ++ tailWord_5720597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720597).length < 2 ^ (prefixWord ++ tailWord_5720597).sum := by decide
  have hdescent : baseEnd_5720597 < baseStart_5720597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720638 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5720638 : Nat := 118140960795 + 5720638 * 2 ^ 59
def prefixEnd_5720638 : Nat := 4983230072969 + 3 ^ 40 * 5720638 * 2
def baseEnd_5720638 : Nat := 2937436944375294211216271

theorem tailTrace_5720638 : CollatzResearch.WordTrace tailWord_5720638 prefixEnd_5720638 2937436944375294211216271 := by
  unfold tailWord_5720638
  simp only [CollatzResearch.WordTrace]
  refine ⟨26081101131139126003999321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139099206032742005354663045 26081101131139126003999321)
  ·
    refine ⟨19560825848354344502999491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26081101131139126003999321 19560825848354344502999491)
    ·
      refine ⟨29341238772531516754499237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19560825848354344502999491 29341238772531516754499237)
      ·
        refine ⟨5501482269849659391468607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29341238772531516754499237 5501482269849659391468607)
        ·
          refine ⟨8252223404774489087202911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501482269849659391468607 8252223404774489087202911)
          ·
            refine ⟨12378335107161733630804367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8252223404774489087202911 12378335107161733630804367)
            ·
              refine ⟨18567502660742600446206551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12378335107161733630804367 18567502660742600446206551)
              ·
                refine ⟨27851253991113900669309827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18567502660742600446206551 27851253991113900669309827)
                ·
                  refine ⟨41776880986670851003964741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27851253991113900669309827 41776880986670851003964741)
                  ·
                    refine ⟨7833165185000784563243389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41776880986670851003964741 7833165185000784563243389)
                    ·
                      refine ⟨2937436944375294211216271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7833165185000784563243389 2937436944375294211216271)
                      ·
                        rfl

theorem cell23_5720638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5720638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720638 prefixEnd_5720638 := by exact prefixLift 5720638
  have htrace : WordTrace (prefixWord ++ tailWord_5720638) baseStart_5720638 baseEnd_5720638 := by
    simpa [prefixWord, tailWord_5720638, baseEnd_5720638] using wordTrace_append hprefix tailTrace_5720638
  have hstable : (prefixWord ++ tailWord_5720638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720638).length < 2 ^ (prefixWord ++ tailWord_5720638).sum := by decide
  have hdescent : baseEnd_5720638 < baseStart_5720638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720661 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_5720661 : Nat := 118140960795 + 5720661 * 2 ^ 59
def prefixEnd_5720661 : Nat := 4983230072969 + 3 ^ 40 * 5720661 * 2
def baseEnd_5720661 : Nat := 2937448754430347621228665

theorem tailTrace_5720661 : CollatzResearch.WordTrace tailWord_5720661 prefixEnd_5720661 2937448754430347621228665 := by
  unfold tailWord_5720661
  simp only [CollatzResearch.WordTrace]
  refine ⟨208649647928029682960081837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139099765285353121973387891 208649647928029682960081837)
  ·
    refine ⟨78243617973011131110030689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208649647928029682960081837 78243617973011131110030689)
    ·
      refine ⟨58682713479758348332523017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78243617973011131110030689 58682713479758348332523017)
      ·
        refine ⟨44012035109818761249392263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58682713479758348332523017 44012035109818761249392263)
        ·
          refine ⟨66018052664728141874088395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44012035109818761249392263 66018052664728141874088395)
          ·
            refine ⟨99027078997092212811132593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66018052664728141874088395 99027078997092212811132593)
            ·
              refine ⟨74270309247819159608349445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99027078997092212811132593 74270309247819159608349445)
              ·
                refine ⟨13925682983966092426565521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74270309247819159608349445 13925682983966092426565521)
                ·
                  refine ⟨10444262237974569319924141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13925682983966092426565521 10444262237974569319924141)
                  ·
                    refine ⟨3916598339240463494971553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10444262237974569319924141 3916598339240463494971553)
                    ·
                      refine ⟨2937448754430347621228665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916598339240463494971553 2937448754430347621228665)
                      ·
                        rfl

theorem cell23_5720661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_5720661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720661 prefixEnd_5720661 := by exact prefixLift 5720661
  have htrace : WordTrace (prefixWord ++ tailWord_5720661) baseStart_5720661 baseEnd_5720661 := by
    simpa [prefixWord, tailWord_5720661, baseEnd_5720661] using wordTrace_append hprefix tailTrace_5720661
  have hstable : (prefixWord ++ tailWord_5720661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720661).length < 2 ^ (prefixWord ++ tailWord_5720661).sum := by decide
  have hdescent : baseEnd_5720661 < baseStart_5720661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720684 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_5720684 : Nat := 118140960795 + 5720684 * 2 ^ 59
def prefixEnd_5720684 : Nat := 4983230072969 + 3 ^ 40 * 5720684 * 2
def baseEnd_5720684 : Nat := 979153521495133677080353

theorem tailTrace_5720684 : CollatzResearch.WordTrace tailWord_5720684 prefixEnd_5720684 979153521495133677080353 := by
  unfold tailWord_5720684
  simp only [CollatzResearch.WordTrace]
  refine ⟨104325243403473178944084553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139100324537964238592112737 104325243403473178944084553)
  ·
    refine ⟨78243932552604884208063415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104325243403473178944084553 78243932552604884208063415)
    ·
      refine ⟨117365898828907326312095123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78243932552604884208063415 117365898828907326312095123)
      ·
        refine ⟨176048848243360989468142685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117365898828907326312095123 176048848243360989468142685)
        ·
          refine ⟨66018318091260371050553507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176048848243360989468142685 66018318091260371050553507)
          ·
            refine ⟨99027477136890556575830261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66018318091260371050553507 99027477136890556575830261)
            ·
              refine ⟨9283825981583489678984087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99027477136890556575830261 9283825981583489678984087)
              ·
                refine ⟨13925738972375234518476131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9283825981583489678984087 13925738972375234518476131)
                ·
                  refine ⟨20888608458562851777714197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13925738972375234518476131 20888608458562851777714197)
                  ·
                    refine ⟨979153521495133677080353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20888608458562851777714197 979153521495133677080353)
                    ·
                      rfl

theorem cell23_5720684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_5720684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720684 prefixEnd_5720684 := by exact prefixLift 5720684
  have htrace : WordTrace (prefixWord ++ tailWord_5720684) baseStart_5720684 baseEnd_5720684 := by
    simpa [prefixWord, tailWord_5720684, baseEnd_5720684] using wordTrace_append hprefix tailTrace_5720684
  have hstable : (prefixWord ++ tailWord_5720684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720684).length < 2 ^ (prefixWord ++ tailWord_5720684).sum := by decide
  have hdescent : baseEnd_5720684 < baseStart_5720684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720691 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 5, 2, 2]
def baseStart_5720691 : Nat := 118140960795 + 5720691 * 2 ^ 59
def prefixEnd_5720691 : Nat := 4983230072969 + 3 ^ 40 * 5720691 * 2
def baseEnd_5720691 : Nat := 2937464158849982503853527

theorem tailTrace_5720691 : CollatzResearch.WordTrace tailWord_5720691 prefixEnd_5720691 2937464158849982503853527 := by
  unfold tailWord_5720691
  simp only [CollatzResearch.WordTrace]
  refine ⟨208650742117920998083673927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139100494745280665389115951 208650742117920998083673927)
  ·
    refine ⟨312976113176881497125510891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208650742117920998083673927 312976113176881497125510891)
    ·
      refine ⟨469464169765322245688266337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312976113176881497125510891 469464169765322245688266337)
      ·
        refine ⟨352098127323991684266199753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469464169765322245688266337 352098127323991684266199753)
        ·
          refine ⟨264073595492993763199649815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352098127323991684266199753 264073595492993763199649815)
          ·
            refine ⟨396110393239490644799474723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264073595492993763199649815 396110393239490644799474723)
            ·
              refine ⟨594165589859235967199212085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396110393239490644799474723 594165589859235967199212085)
              ·
                refine ⟨55703024049303371924926133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 594165589859235967199212085 55703024049303371924926133)
                ·
                  refine ⟨5222158504622191117961825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55703024049303371924926133 5222158504622191117961825)
                  ·
                    refine ⟨3916618878466643338471369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5222158504622191117961825 3916618878466643338471369)
                    ·
                      refine ⟨2937464158849982503853527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916618878466643338471369 2937464158849982503853527)
                      ·
                        rfl

theorem cell23_5720691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 2, 2].length) (baseStart_5720691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720691 prefixEnd_5720691 := by exact prefixLift 5720691
  have htrace : WordTrace (prefixWord ++ tailWord_5720691) baseStart_5720691 baseEnd_5720691 := by
    simpa [prefixWord, tailWord_5720691, baseEnd_5720691] using wordTrace_append hprefix tailTrace_5720691
  have hstable : (prefixWord ++ tailWord_5720691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720691).length < 2 ^ (prefixWord ++ tailWord_5720691).sum := by decide
  have hdescent : baseEnd_5720691 < baseStart_5720691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720711 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_5720711 : Nat := 118140960795 + 5720711 * 2 ^ 59
def prefixEnd_5720711 : Nat := 4983230072969 + 3 ^ 40 * 5720711 * 2
def baseEnd_5720711 : Nat := 2937474428463072425603435

theorem tailTrace_5720711 : CollatzResearch.WordTrace tailWord_5720711 prefixEnd_5720711 2937474428463072425603435 := by
  unfold tailWord_5720711
  simp only [CollatzResearch.WordTrace]
  refine ⟨208651471577848541499401987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139100981051899027666267991 208651471577848541499401987)
  ·
    refine ⟨312977207366772812249102981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208651471577848541499401987 312977207366772812249102981)
    ·
      refine ⟨58683226381269902296706809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312977207366772812249102981 58683226381269902296706809)
      ·
        refine ⟨44012419785952426722530107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58683226381269902296706809 44012419785952426722530107)
        ·
          refine ⟨66018629678928640083795161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44012419785952426722530107 66018629678928640083795161)
          ·
            refine ⟨49513972259196480062846371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66018629678928640083795161 49513972259196480062846371)
            ·
              refine ⟨74270958388794720094269557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49513972259196480062846371 74270958388794720094269557)
              ·
                refine ⟨6962902348949505008837771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74270958388794720094269557 6962902348949505008837771)
                ·
                  refine ⟨10444353523424257513256657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6962902348949505008837771 10444353523424257513256657)
                  ·
                    refine ⟨7833265142568193134942493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10444353523424257513256657 7833265142568193134942493)
                    ·
                      refine ⟨2937474428463072425603435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7833265142568193134942493 2937474428463072425603435)
                      ·
                        rfl

theorem cell23_5720711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_5720711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720711 prefixEnd_5720711 := by exact prefixLift 5720711
  have htrace : WordTrace (prefixWord ++ tailWord_5720711) baseStart_5720711 baseEnd_5720711 := by
    simpa [prefixWord, tailWord_5720711, baseEnd_5720711] using wordTrace_append hprefix tailTrace_5720711
  have hstable : (prefixWord ++ tailWord_5720711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720711).length < 2 ^ (prefixWord ++ tailWord_5720711).sum := by decide
  have hdescent : baseEnd_5720711 < baseStart_5720711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720804 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 9]
def baseStart_5720804 : Nat := 118140960795 + 5720804 * 2 ^ 59
def prefixEnd_5720804 : Nat := 4983230072969 + 3 ^ 40 * 5720804 * 2
def baseEnd_5720804 : Nat := 326391353573771173526723

theorem tailTrace_5720804 : CollatzResearch.WordTrace tailWord_5720804 prefixEnd_5720804 326391353573771173526723 := by
  unfold tailWord_5720804
  simp only [CollatzResearch.WordTrace]
  refine ⟨104327431783255809191268733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139103242377674412255024977 104327431783255809191268733)
  ·
    refine ⟨39122786918720928446725775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104327431783255809191268733 39122786918720928446725775)
    ·
      refine ⟨58684180378081392670088663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39122786918720928446725775 58684180378081392670088663)
      ·
        refine ⟨88026270567122089005132995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58684180378081392670088663 88026270567122089005132995)
        ·
          refine ⟨132039405850683133507699493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88026270567122089005132995 132039405850683133507699493)
          ·
            refine ⟨24757388597003087532693655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132039405850683133507699493 24757388597003087532693655)
            ·
              refine ⟨37136082895504631299040483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24757388597003087532693655 37136082895504631299040483)
              ·
                refine ⟨55704124343256946948560725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37136082895504631299040483 55704124343256946948560725)
                ·
                  refine ⟨326391353573771173526723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55704124343256946948560725 326391353573771173526723)
                  ·
                    rfl

theorem cell23_5720804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_5720804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720804 prefixEnd_5720804 := by exact prefixLift 5720804
  have htrace : WordTrace (prefixWord ++ tailWord_5720804) baseStart_5720804 baseEnd_5720804 := by
    simpa [prefixWord, tailWord_5720804, baseEnd_5720804] using wordTrace_append hprefix tailTrace_5720804
  have hstable : (prefixWord ++ tailWord_5720804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720804).length < 2 ^ (prefixWord ++ tailWord_5720804).sum := by decide
  have hdescent : baseEnd_5720804 < baseStart_5720804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720841 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 7, 2]
def baseStart_5720841 : Nat := 118140960795 + 5720841 * 2 ^ 59
def prefixEnd_5720841 : Nat := 4983230072969 + 3 ^ 40 * 5720841 * 2
def baseEnd_5720841 : Nat := 2937541180948156916977837

theorem tailTrace_5720841 : CollatzResearch.WordTrace tailWord_5720841 prefixEnd_5720841 2937541180948156916977837 := by
  unfold tailWord_5720841
  simp only [CollatzResearch.WordTrace]
  refine ⟨208656213067377573701634377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139104142044918382467756251 208656213067377573701634377)
  ·
    refine ⟨156492159800533180276225783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208656213067377573701634377 156492159800533180276225783)
    ·
      refine ⟨234738239700799770414338675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156492159800533180276225783 234738239700799770414338675)
      ·
        refine ⟨352107359551199655621508013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234738239700799770414338675 352107359551199655621508013)
        ·
          refine ⟨132040259831699870858065505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352107359551199655621508013 132040259831699870858065505)
          ·
            refine ⟨99030194873774903143549129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132040259831699870858065505 99030194873774903143549129)
            ·
              refine ⟨74272646155331177357661847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99030194873774903143549129 74272646155331177357661847)
              ·
                refine ⟨111408969232996766036492771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74272646155331177357661847 111408969232996766036492771)
                ·
                  refine ⟨167113453849495149054739157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111408969232996766036492771 167113453849495149054739157)
                  ·
                    refine ⟨3916721574597542555970449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167113453849495149054739157 3916721574597542555970449)
                    ·
                      refine ⟨2937541180948156916977837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916721574597542555970449 2937541180948156916977837)
                      ·
                        rfl

theorem cell23_5720841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 7, 2].length) (baseStart_5720841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720841 prefixEnd_5720841 := by exact prefixLift 5720841
  have htrace : WordTrace (prefixWord ++ tailWord_5720841) baseStart_5720841 baseEnd_5720841 := by
    simpa [prefixWord, tailWord_5720841, baseEnd_5720841] using wordTrace_append hprefix tailTrace_5720841
  have hstable : (prefixWord ++ tailWord_5720841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720841).length < 2 ^ (prefixWord ++ tailWord_5720841).sum := by decide
  have hdescent : baseEnd_5720841 < baseStart_5720841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720844 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5720844 : Nat := 118140960795 + 5720844 * 2 ^ 59
def prefixEnd_5720844 : Nat := 4983230072969 + 3 ^ 40 * 5720844 * 2
def baseEnd_5720844 : Nat := 2937542721390120405240323

theorem tailTrace_5720844 : CollatzResearch.WordTrace tailWord_5720844 prefixEnd_5720844 2937542721390120405240323 := by
  unfold tailWord_5720844
  simp only [CollatzResearch.WordTrace]
  refine ⟨104328161243183352606996793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139104214990911136809329057 104328161243183352606996793)
  ·
    refine ⟨78246120932387514455247595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104328161243183352606996793 78246120932387514455247595)
    ·
      refine ⟨117369181398581271682871393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78246120932387514455247595 117369181398581271682871393)
      ·
        refine ⟨88026886048935953762153545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117369181398581271682871393 88026886048935953762153545)
        ·
          refine ⟨66020164536701965321615159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88026886048935953762153545 66020164536701965321615159)
          ·
            refine ⟨99030246805052947982422739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66020164536701965321615159 99030246805052947982422739)
            ·
              refine ⟨148545370207579421973634109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99030246805052947982422739 148545370207579421973634109)
              ·
                refine ⟨55704513827842283240112791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148545370207579421973634109 55704513827842283240112791)
                ·
                  refine ⟨83556770741763424860169187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55704513827842283240112791 83556770741763424860169187)
                  ·
                    refine ⟨125335156112645137290253781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83556770741763424860169187 125335156112645137290253781)
                    ·
                      refine ⟨2937542721390120405240323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125335156112645137290253781 2937542721390120405240323)
                      ·
                        rfl

theorem cell23_5720844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5720844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720844 prefixEnd_5720844 := by exact prefixLift 5720844
  have htrace : WordTrace (prefixWord ++ tailWord_5720844) baseStart_5720844 baseEnd_5720844 := by
    simpa [prefixWord, tailWord_5720844, baseEnd_5720844] using wordTrace_append hprefix tailTrace_5720844
  have hstable : (prefixWord ++ tailWord_5720844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720844).length < 2 ^ (prefixWord ++ tailWord_5720844).sum := by decide
  have hdescent : baseEnd_5720844 < baseStart_5720844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720949 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5720949 : Nat := 118140960795 + 5720949 * 2 ^ 59
def prefixEnd_5720949 : Nat := 4983230072969 + 3 ^ 40 * 5720949 * 2
def baseEnd_5720949 : Nat := 979198878952947498142447

theorem tailTrace_5720949 : CollatzResearch.WordTrace tailWord_5720949 prefixEnd_5720949 979198878952947498142447 := by
  unfold tailWord_5720949
  simp only [CollatzResearch.WordTrace]
  refine ⟨208660152150986308146565901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139106768100657538764377267 208660152150986308146565901)
  ·
    refine ⟨78247557056619865554962213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208660152150986308146565901 78247557056619865554962213)
    ·
      refine ⟨14671416948116224791555415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78247557056619865554962213 14671416948116224791555415)
      ·
        refine ⟨22007125422174337187333123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14671416948116224791555415 22007125422174337187333123)
        ·
          refine ⟨33010688133261505780999685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22007125422174337187333123 33010688133261505780999685)
          ·
            refine ⟨6189504024986532333937441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33010688133261505780999685 6189504024986532333937441)
            ·
              refine ⟨4642128018739899250453081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6189504024986532333937441 4642128018739899250453081)
              ·
                refine ⟨3481596014054924437839811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4642128018739899250453081 3481596014054924437839811)
                ·
                  refine ⟨5222394021082386656759717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481596014054924437839811 5222394021082386656759717)
                  ·
                    refine ⟨979198878952947498142447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5222394021082386656759717 979198878952947498142447)
                    ·
                      rfl

theorem cell23_5720949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5720949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720949 prefixEnd_5720949 := by exact prefixLift 5720949
  have htrace : WordTrace (prefixWord ++ tailWord_5720949) baseStart_5720949 baseEnd_5720949 := by
    simpa [prefixWord, tailWord_5720949, baseEnd_5720949] using wordTrace_append hprefix tailTrace_5720949
  have hstable : (prefixWord ++ tailWord_5720949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720949).length < 2 ^ (prefixWord ++ tailWord_5720949).sum := by decide
  have hdescent : baseEnd_5720949 < baseStart_5720949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720971 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 1, 6]
def baseStart_5720971 : Nat := 118140960795 + 5720971 * 2 ^ 59
def prefixEnd_5720971 : Nat := 4983230072969 + 3 ^ 40 * 5720971 * 2
def baseEnd_5720971 : Nat := 979202644477747136117413

theorem tailTrace_5720971 : CollatzResearch.WordTrace tailWord_5720971 prefixEnd_5720971 979202644477747136117413 := by
  unfold tailWord_5720971
  simp only [CollatzResearch.WordTrace]
  refine ⟨208660954556906605903866767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139107303037937737269244511 208660954556906605903866767)
  ·
    refine ⟨312991431835359908855800151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208660954556906605903866767 312991431835359908855800151)
    ·
      refine ⟨469487147753039863283700227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312991431835359908855800151 469487147753039863283700227)
      ·
        refine ⟨704230721629559794925550341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469487147753039863283700227 704230721629559794925550341)
        ·
          refine ⟨132043260305542461548540689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 704230721629559794925550341 132043260305542461548540689)
          ·
            refine ⟨99032445229156846161405517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132043260305542461548540689 99032445229156846161405517)
            ·
              refine ⟨37137166960933817310527069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99032445229156846161405517 37137166960933817310527069)
              ·
                refine ⟨13926437610350181491447651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37137166960933817310527069 13926437610350181491447651)
                ·
                  refine ⟨20889656415525272237171477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926437610350181491447651 20889656415525272237171477)
                  ·
                    refine ⟨979202644477747136117413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20889656415525272237171477 979202644477747136117413)
                    ·
                      rfl

theorem cell23_5720971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 6].length) (baseStart_5720971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720971 prefixEnd_5720971 := by exact prefixLift 5720971
  have htrace : WordTrace (prefixWord ++ tailWord_5720971) baseStart_5720971 baseEnd_5720971 := by
    simpa [prefixWord, tailWord_5720971, baseEnd_5720971] using wordTrace_append hprefix tailTrace_5720971
  have hstable : (prefixWord ++ tailWord_5720971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720971).length < 2 ^ (prefixWord ++ tailWord_5720971).sum := by decide
  have hdescent : baseEnd_5720971 < baseStart_5720971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5720995 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 1, 1, 4]
def baseStart_5720995 : Nat := 118140960795 + 5720995 * 2 ^ 59
def prefixEnd_5720995 : Nat := 4983230072969 + 3 ^ 40 * 5720995 * 2
def baseEnd_5720995 : Nat := 2937620256968949314452129

theorem tailTrace_5720995 : CollatzResearch.WordTrace tailWord_5720995 prefixEnd_5720995 2937620256968949314452129 := by
  unfold tailWord_5720995
  simp only [CollatzResearch.WordTrace]
  refine ⟨208661829908819658002740439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139107886605879772001826959 208661829908819658002740439)
  ·
    refine ⟨312992744863229487004110659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208661829908819658002740439 312992744863229487004110659)
    ·
      refine ⟨469489117294844230506165989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312992744863229487004110659 469489117294844230506165989)
      ·
        refine ⟨88029209492783293219906123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469489117294844230506165989 88029209492783293219906123)
        ·
          refine ⟨132043814239174939829859185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88029209492783293219906123 132043814239174939829859185)
          ·
            refine ⟨99032860679381204872394389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132043814239174939829859185 99032860679381204872394389)
            ·
              refine ⟨4642165344345993978393487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99032860679381204872394389 4642165344345993978393487)
              ·
                refine ⟨6963248016518990967590231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642165344345993978393487 6963248016518990967590231)
                ·
                  refine ⟨10444872024778486451385347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963248016518990967590231 10444872024778486451385347)
                  ·
                    refine ⟨15667308037167729677078021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10444872024778486451385347 15667308037167729677078021)
                    ·
                      refine ⟨2937620256968949314452129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15667308037167729677078021 2937620256968949314452129)
                      ·
                        rfl

theorem cell23_5720995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_5720995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5720995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5720995 prefixEnd_5720995 := by exact prefixLift 5720995
  have htrace : WordTrace (prefixWord ++ tailWord_5720995) baseStart_5720995 baseEnd_5720995 := by
    simpa [prefixWord, tailWord_5720995, baseEnd_5720995] using wordTrace_append hprefix tailTrace_5720995
  have hstable : (prefixWord ++ tailWord_5720995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5720995).length < 2 ^ (prefixWord ++ tailWord_5720995).sum := by decide
  have hdescent : baseEnd_5720995 < baseStart_5720995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5720995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721022 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_5721022 : Nat := 118140960795 + 5721022 * 2 ^ 59
def prefixEnd_5721022 : Nat := 4983230072969 + 3 ^ 40 * 5721022 * 2
def baseEnd_5721022 : Nat := 979211373648873569604835

theorem tailTrace_5721022 : CollatzResearch.WordTrace tailWord_5721022 prefixEnd_5721022 979211373648873569604835 := by
  unfold tailWord_5721022
  simp only [CollatzResearch.WordTrace]
  refine ⟨26082851834965230201746665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139108543119814561075982213 26082851834965230201746665)
  ·
    refine ⟨19562138876223922651309999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26082851834965230201746665 19562138876223922651309999)
    ·
      refine ⟨29343208314335883976964999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19562138876223922651309999 29343208314335883976964999)
      ·
        refine ⟨44014812471503825965447499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29343208314335883976964999 44014812471503825965447499)
        ·
          refine ⟨66022218707255738948171249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44014812471503825965447499 66022218707255738948171249)
          ·
            refine ⟨49516664030441804211128437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66022218707255738948171249 49516664030441804211128437)
            ·
              refine ⟨4642187252853919144793291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49516664030441804211128437 4642187252853919144793291)
              ·
                refine ⟨6963280879280878717189937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642187252853919144793291 6963280879280878717189937)
                ·
                  refine ⟨5222460659460659037892453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6963280879280878717189937 5222460659460659037892453)
                  ·
                    refine ⟨979211373648873569604835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5222460659460659037892453 979211373648873569604835)
                    ·
                      rfl

theorem cell23_5721022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_5721022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721022 prefixEnd_5721022 := by exact prefixLift 5721022
  have htrace : WordTrace (prefixWord ++ tailWord_5721022) baseStart_5721022 baseEnd_5721022 := by
    simpa [prefixWord, tailWord_5721022, baseEnd_5721022] using wordTrace_append hprefix tailTrace_5721022
  have hstable : (prefixWord ++ tailWord_5721022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721022).length < 2 ^ (prefixWord ++ tailWord_5721022).sum := by decide
  have hdescent : baseEnd_5721022 < baseStart_5721022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721031 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 2, 7]
def baseStart_5721031 : Nat := 118140960795 + 5721031 * 2 ^ 59
def prefixEnd_5721031 : Nat := 4983230072969 + 3 ^ 40 * 5721031 * 2
def baseEnd_5721031 : Nat := 979212914090837057867321

theorem tailTrace_5721031 : CollatzResearch.WordTrace tailWord_5721031 prefixEnd_5721031 979212914090837057867321 := by
  unfold tailWord_5721031
  simp only [CollatzResearch.WordTrace]
  refine ⟨208663142936689236151050947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139108761957792824100700631 208663142936689236151050947)
  ·
    refine ⟨312994714405033854226576421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208663142936689236151050947 312994714405033854226576421)
    ·
      refine ⟨58686508950943847667483079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312994714405033854226576421 58686508950943847667483079)
      ·
        refine ⟨88029763426415771501224619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58686508950943847667483079 88029763426415771501224619)
        ·
          refine ⟨132044645139623657251836929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88029763426415771501224619 132044645139623657251836929)
          ·
            refine ⟨99033483854717742938877697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132044645139623657251836929 99033483854717742938877697)
            ·
              refine ⟨74275112891038307204158273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99033483854717742938877697 74275112891038307204158273)
              ·
                refine ⟨55706334668278730403118705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74275112891038307204158273 55706334668278730403118705)
                ·
                  refine ⟨41779751001209047802339029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55706334668278730403118705 41779751001209047802339029)
                  ·
                    refine ⟨979212914090837057867321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41779751001209047802339029 979212914090837057867321)
                    ·
                      rfl

theorem cell23_5721031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_5721031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721031 prefixEnd_5721031 := by exact prefixLift 5721031
  have htrace : WordTrace (prefixWord ++ tailWord_5721031) baseStart_5721031 baseEnd_5721031 := by
    simpa [prefixWord, tailWord_5721031, baseEnd_5721031] using wordTrace_append hprefix tailTrace_5721031
  have hstable : (prefixWord ++ tailWord_5721031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721031).length < 2 ^ (prefixWord ++ tailWord_5721031).sum := by decide
  have hdescent : baseEnd_5721031 < baseStart_5721031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721032 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_5721032 : Nat := 118140960795 + 5721032 * 2 ^ 59
def prefixEnd_5721032 : Nat := 4983230072969 + 3 ^ 40 * 5721032 * 2
def baseEnd_5721032 : Nat := 2937639255753165669689459

theorem tailTrace_5721032 : CollatzResearch.WordTrace tailWord_5721032 prefixEnd_5721032 2937639255753165669689459 := by
  unfold tailWord_5721032
  simp only [CollatzResearch.WordTrace]
  refine ⟨104331589704842806660918675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139108786273123742214558233 104331589704842806660918675)
  ·
    refine ⟨156497384557264209991378013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104331589704842806660918675 156497384557264209991378013)
    ·
      refine ⟨58686519208974078746766755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156497384557264209991378013 58686519208974078746766755)
      ·
        refine ⟨88029778813461118120150133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58686519208974078746766755 88029778813461118120150133)
        ·
          refine ⟨8252791763761979823764075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88029778813461118120150133 8252791763761979823764075)
          ·
            refine ⟨12379187645642969735646113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8252791763761979823764075 12379187645642969735646113)
            ·
              refine ⟨9284390734232227301734585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12379187645642969735646113 9284390734232227301734585)
              ·
                refine ⟨6963293050674170476300939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9284390734232227301734585 6963293050674170476300939)
                ·
                  refine ⟨10444939576011255714451409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963293050674170476300939 10444939576011255714451409)
                  ·
                    refine ⟨7833704682008441785838557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10444939576011255714451409 7833704682008441785838557)
                    ·
                      refine ⟨2937639255753165669689459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7833704682008441785838557 2937639255753165669689459)
                      ·
                        rfl

theorem cell23_5721032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_5721032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721032 prefixEnd_5721032 := by exact prefixLift 5721032
  have htrace : WordTrace (prefixWord ++ tailWord_5721032) baseStart_5721032 baseEnd_5721032 := by
    simpa [prefixWord, tailWord_5721032, baseEnd_5721032] using wordTrace_append hprefix tailTrace_5721032
  have hstable : (prefixWord ++ tailWord_5721032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721032).length < 2 ^ (prefixWord ++ tailWord_5721032).sum := by decide
  have hdescent : baseEnd_5721032 < baseStart_5721032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721041 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_5721041 : Nat := 118140960795 + 5721041 * 2 ^ 59
def prefixEnd_5721041 : Nat := 4983230072969 + 3 ^ 40 * 5721041 * 2
def baseEnd_5721041 : Nat := 2937643877079056134476917

theorem tailTrace_5721041 : CollatzResearch.WordTrace tailWord_5721041 prefixEnd_5721041 2937643877079056134476917 := by
  unfold tailWord_5721041
  simp only [CollatzResearch.WordTrace]
  refine ⟨208663507666653007858914977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139109005111102005239276651 208663507666653007858914977)
  ·
    refine ⟨156497630749989755894186233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208663507666653007858914977 156497630749989755894186233)
    ·
      refine ⟨117373223062492316920639675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156497630749989755894186233 117373223062492316920639675)
      ·
        refine ⟨176059834593738475380959513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117373223062492316920639675 176059834593738475380959513)
        ·
          refine ⟨132044875945303856535719635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176059834593738475380959513 132044875945303856535719635)
          ·
            refine ⟨198067313917955784803579453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132044875945303856535719635 198067313917955784803579453)
            ·
              refine ⟨74275242719233419301342295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198067313917955784803579453 74275242719233419301342295)
              ·
                refine ⟨111412864078850128952013443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74275242719233419301342295 111412864078850128952013443)
                ·
                  refine ⟨167119296118275193428020165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111412864078850128952013443 167119296118275193428020165)
                  ·
                    refine ⟨31334868022176598767753781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167119296118275193428020165 31334868022176598767753781)
                    ·
                      refine ⟨2937643877079056134476917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31334868022176598767753781 2937643877079056134476917)
                      ·
                        rfl

theorem cell23_5721041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_5721041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721041 prefixEnd_5721041 := by exact prefixLift 5721041
  have htrace : WordTrace (prefixWord ++ tailWord_5721041) baseStart_5721041 baseEnd_5721041 := by
    simpa [prefixWord, tailWord_5721041, baseEnd_5721041] using wordTrace_append hprefix tailTrace_5721041
  have hstable : (prefixWord ++ tailWord_5721041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721041).length < 2 ^ (prefixWord ++ tailWord_5721041).sum := by decide
  have hdescent : baseEnd_5721041 < baseStart_5721041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721085 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_5721085 : Nat := 118140960795 + 5721085 * 2 ^ 59
def prefixEnd_5721085 : Nat := 4983230072969 + 3 ^ 40 * 5721085 * 2
def baseEnd_5721085 : Nat := 2937666470227853962326715

theorem tailTrace_5721085 : CollatzResearch.WordTrace tailWord_5721085 prefixEnd_5721085 2937666470227853962326715 := by
  unfold tailWord_5721085
  simp only [CollatzResearch.WordTrace]
  refine ⟨208665112478493603373516709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139110074985662402249011139 208665112478493603373516709)
  ·
    refine ⟨39124708589717550632534383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208665112478493603373516709 39124708589717550632534383)
    ·
      refine ⟨58687062884576325948801575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39124708589717550632534383 58687062884576325948801575)
      ·
        refine ⟨88030594326864488923202363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58687062884576325948801575 88030594326864488923202363)
        ·
          refine ⟨132045891490296733384803545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88030594326864488923202363 132045891490296733384803545)
          ·
            refine ⟨99034418617722550038602659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132045891490296733384803545 99034418617722550038602659)
            ·
              refine ⟨148551627926583825057903989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99034418617722550038602659 148551627926583825057903989)
              ·
                refine ⟨13926715118117233599178499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148551627926583825057903989 13926715118117233599178499)
                ·
                  refine ⟨20890072677175850398767749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926715118117233599178499 20890072677175850398767749)
                  ·
                    refine ⟨3916888626970471949768953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20890072677175850398767749 3916888626970471949768953)
                    ·
                      refine ⟨2937666470227853962326715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916888626970471949768953 2937666470227853962326715)
                      ·
                        rfl

theorem cell23_5721085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_5721085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721085 prefixEnd_5721085 := by exact prefixLift 5721085
  have htrace : WordTrace (prefixWord ++ tailWord_5721085) baseStart_5721085 baseEnd_5721085 := by
    simpa [prefixWord, tailWord_5721085, baseEnd_5721085] using wordTrace_append hprefix tailTrace_5721085
  have hstable : (prefixWord ++ tailWord_5721085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721085).length < 2 ^ (prefixWord ++ tailWord_5721085).sum := by decide
  have hdescent : baseEnd_5721085 < baseStart_5721085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721089 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_5721089 : Nat := 118140960795 + 5721089 * 2 ^ 59
def prefixEnd_5721089 : Nat := 4983230072969 + 3 ^ 40 * 5721089 * 2
def baseEnd_5721089 : Nat := 2937668524150471946676697

theorem tailTrace_5721089 : CollatzResearch.WordTrace tailWord_5721089 prefixEnd_5721089 2937668524150471946676697 := by
  unfold tailWord_5721089
  simp only [CollatzResearch.WordTrace]
  refine ⟨208665258370479112056662321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139110172246986074704441547 208665258370479112056662321)
  ·
    refine ⟨156498943777859334042496741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208665258370479112056662321 156498943777859334042496741)
    ·
      refine ⟨29343551958348625132968139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156498943777859334042496741 29343551958348625132968139)
      ·
        refine ⟨44015327937522937699452209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29343551958348625132968139 44015327937522937699452209)
        ·
          refine ⟨33011495953142203274589157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44015327937522937699452209 33011495953142203274589157)
          ·
            refine ⟨6189655491214163113985467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33011495953142203274589157 6189655491214163113985467)
            ·
              refine ⟨9284483236821244670978201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6189655491214163113985467 9284483236821244670978201)
              ·
                refine ⟨6963362427615933503233651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9284483236821244670978201 6963362427615933503233651)
                ·
                  refine ⟨10445043641423900254850477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963362427615933503233651 10445043641423900254850477)
                  ·
                    refine ⟨3916891365533962595568929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10445043641423900254850477 3916891365533962595568929)
                    ·
                      refine ⟨2937668524150471946676697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916891365533962595568929 2937668524150471946676697)
                      ·
                        rfl

theorem cell23_5721089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_5721089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721089 prefixEnd_5721089 := by exact prefixLift 5721089
  have htrace : WordTrace (prefixWord ++ tailWord_5721089) baseStart_5721089 baseEnd_5721089 := by
    simpa [prefixWord, tailWord_5721089, baseEnd_5721089] using wordTrace_append hprefix tailTrace_5721089
  have hstable : (prefixWord ++ tailWord_5721089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721089).length < 2 ^ (prefixWord ++ tailWord_5721089).sum := by decide
  have hdescent : baseEnd_5721089 < baseStart_5721089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721102 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_5721102 : Nat := 118140960795 + 5721102 * 2 ^ 59
def prefixEnd_5721102 : Nat := 4983230072969 + 3 ^ 40 * 5721102 * 2
def baseEnd_5721102 : Nat := 2937675199398980395814137

theorem tailTrace_5721102 : CollatzResearch.WordTrace tailWord_5721102 prefixEnd_5721102 2937675199398980395814137 := by
  unfold tailWord_5721102
  simp only [CollatzResearch.WordTrace]
  refine ⟨26083216564929001909610695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139110488346288010184590373 26083216564929001909610695)
  ·
    refine ⟨39124824847393502864416043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26083216564929001909610695 39124824847393502864416043)
    ·
      refine ⟨58687237271090254296624065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39124824847393502864416043 58687237271090254296624065)
      ·
        refine ⟨44015427953317690722468049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58687237271090254296624065 44015427953317690722468049)
        ·
          refine ⟨33011570964988268041851037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44015427953317690722468049 33011570964988268041851037)
          ·
            refine ⟨12379339111870600515694139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33011570964988268041851037 12379339111870600515694139)
            ·
              refine ⟨18569008667805900773541209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12379339111870600515694139 18569008667805900773541209)
              ·
                refine ⟨13926756500854425580155907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18569008667805900773541209 13926756500854425580155907)
                ·
                  refine ⟨20890134751281638370233861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926756500854425580155907 20890134751281638370233861)
                  ·
                    refine ⟨3916900265865307194418849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20890134751281638370233861 3916900265865307194418849)
                    ·
                      refine ⟨2937675199398980395814137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916900265865307194418849 2937675199398980395814137)
                      ·
                        rfl

theorem cell23_5721102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_5721102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721102 prefixEnd_5721102 := by exact prefixLift 5721102
  have htrace : WordTrace (prefixWord ++ tailWord_5721102) baseStart_5721102 baseEnd_5721102 := by
    simpa [prefixWord, tailWord_5721102, baseEnd_5721102] using wordTrace_append hprefix tailTrace_5721102
  have hstable : (prefixWord ++ tailWord_5721102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721102).length < 2 ^ (prefixWord ++ tailWord_5721102).sum := by decide
  have hdescent : baseEnd_5721102 < baseStart_5721102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721119 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 2, 2, 2]
def baseStart_5721119 : Nat := 118140960795 + 5721119 * 2 ^ 59
def prefixEnd_5721119 : Nat := 4983230072969 + 3 ^ 40 * 5721119 * 2
def baseEnd_5721119 : Nat := 2937683928570106829301559

theorem tailTrace_5721119 : CollatzResearch.WordTrace tailWord_5721119 prefixEnd_5721119 2937683928570106829301559 := by
  unfold tailWord_5721119
  simp only [CollatzResearch.WordTrace]
  refine ⟨208666352560370427180254411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139110901706913618120169607 208666352560370427180254411)
  ·
    refine ⟨312999528840555640770381617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208666352560370427180254411 312999528840555640770381617)
    ·
      refine ⟨234749646630416730577786213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312999528840555640770381617 234749646630416730577786213)
      ·
        refine ⟨44015558743203136983334915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234749646630416730577786213 44015558743203136983334915)
        ·
          refine ⟨66023338114804705475002373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44015558743203136983334915 66023338114804705475002373)
          ·
            refine ⟨12379375896525882276562945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66023338114804705475002373 12379375896525882276562945)
            ·
              refine ⟨9284531922394411707422209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12379375896525882276562945 9284531922394411707422209)
              ·
                refine ⟨6963398941795808780566657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9284531922394411707422209 6963398941795808780566657)
                ·
                  refine ⟨5222549206346856585424993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6963398941795808780566657 5222549206346856585424993)
                  ·
                    refine ⟨3916911904760142439068745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5222549206346856585424993 3916911904760142439068745)
                    ·
                      refine ⟨2937683928570106829301559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3916911904760142439068745 2937683928570106829301559)
                      ·
                        rfl

theorem cell23_5721119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_5721119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721119 prefixEnd_5721119 := by exact prefixLift 5721119
  have htrace : WordTrace (prefixWord ++ tailWord_5721119) baseStart_5721119 baseEnd_5721119 := by
    simpa [prefixWord, tailWord_5721119, baseEnd_5721119] using wordTrace_append hprefix tailTrace_5721119
  have hstable : (prefixWord ++ tailWord_5721119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721119).length < 2 ^ (prefixWord ++ tailWord_5721119).sum := by decide
  have hdescent : baseEnd_5721119 < baseStart_5721119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721125 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 5]
def baseStart_5721125 : Nat := 118140960795 + 5721125 * 2 ^ 59
def prefixEnd_5721125 : Nat := 4983230072969 + 3 ^ 40 * 5721125 * 2
def baseEnd_5721125 : Nat := 326409667717114867314059

theorem tailTrace_5721125 : CollatzResearch.WordTrace tailWord_5721125 prefixEnd_5721125 326409667717114867314059 := by
  unfold tailWord_5721125
  simp only [CollatzResearch.WordTrace]
  refine ⟨208666571398348690204972829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139111047598899126803315219 208666571398348690204972829)
  ·
    refine ⟨78249964274380758826864811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208666571398348690204972829 78249964274380758826864811)
    ·
      refine ⟨117374946411571138240297217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78249964274380758826864811 117374946411571138240297217)
      ·
        refine ⟨88031209808678353680222913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117374946411571138240297217 88031209808678353680222913)
        ·
          refine ⟨66023407356508765260167185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88031209808678353680222913 66023407356508765260167185)
          ·
            refine ⟨49517555517381573945125389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66023407356508765260167185 49517555517381573945125389)
            ·
              refine ⟨18569083319018090229422021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49517555517381573945125389 18569083319018090229422021)
              ·
                refine ⟨3481703122315891918016629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18569083319018090229422021 3481703122315891918016629)
                ·
                  refine ⟨326409667717114867314059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481703122315891918016629 326409667717114867314059)
                  ·
                    rfl

theorem cell23_5721125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_5721125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721125 prefixEnd_5721125 := by exact prefixLift 5721125
  have htrace : WordTrace (prefixWord ++ tailWord_5721125) baseStart_5721125 baseEnd_5721125 := by
    simpa [prefixWord, tailWord_5721125, baseEnd_5721125] using wordTrace_append hprefix tailTrace_5721125
  have hstable : (prefixWord ++ tailWord_5721125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721125).length < 2 ^ (prefixWord ++ tailWord_5721125).sum := by decide
  have hdescent : baseEnd_5721125 < baseStart_5721125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721138 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_5721138 : Nat := 118140960795 + 5721138 * 2 ^ 59
def prefixEnd_5721138 : Nat := 4983230072969 + 3 ^ 40 * 5721138 * 2
def baseEnd_5721138 : Nat := 979231228234180751654657

theorem tailTrace_5721138 : CollatzResearch.WordTrace tailWord_5721138 prefixEnd_5721138 979231228234180751654657 := by
  unfold tailWord_5721138
  simp only [CollatzResearch.WordTrace]
  refine ⟨52166761386825398356299017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139111363698201062283464045 52166761386825398356299017)
  ·
    refine ⟨39125071040119048767224263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52166761386825398356299017 39125071040119048767224263)
    ·
      refine ⟨58687606560178573150836395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39125071040119048767224263 58687606560178573150836395)
      ·
        refine ⟨88031409840267859726254593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58687606560178573150836395 88031409840267859726254593)
        ·
          refine ⟨66023557380200894794690945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88031409840267859726254593 66023557380200894794690945)
          ·
            refine ⟨49517668035150671096018209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66023557380200894794690945 49517668035150671096018209)
            ·
              refine ⟨37138251026363003322013657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49517668035150671096018209 37138251026363003322013657)
              ·
                refine ⟨27853688269772252491510243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37138251026363003322013657 27853688269772252491510243)
                ·
                  refine ⟨41780532404658378737265365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27853688269772252491510243 41780532404658378737265365)
                  ·
                    refine ⟨979231228234180751654657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41780532404658378737265365 979231228234180751654657)
                    ·
                      rfl

theorem cell23_5721138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_5721138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721138 prefixEnd_5721138 := by exact prefixLift 5721138
  have htrace : WordTrace (prefixWord ++ tailWord_5721138) baseStart_5721138 baseEnd_5721138 := by
    simpa [prefixWord, tailWord_5721138, baseEnd_5721138] using wordTrace_append hprefix tailTrace_5721138
  have hstable : (prefixWord ++ tailWord_5721138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721138).length < 2 ^ (prefixWord ++ tailWord_5721138).sum := by decide
  have hdescent : baseEnd_5721138 < baseStart_5721138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721185 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 3, 4]
def baseStart_5721185 : Nat := 118140960795 + 5721185 * 2 ^ 59
def prefixEnd_5721185 : Nat := 4983230072969 + 3 ^ 40 * 5721185 * 2
def baseEnd_5721185 : Nat := 979239272764434523692085

theorem tailTrace_5721185 : CollatzResearch.WordTrace tailWord_5721185 prefixEnd_5721185 979239272764434523692085 := by
  unfold tailWord_5721185
  simp only [CollatzResearch.WordTrace]
  refine ⟨208668759778131320452157009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139112506518754213634771339 208668759778131320452157009)
  ·
    refine ⟨156501569833598490339117757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208668759778131320452157009 156501569833598490339117757)
    ·
      refine ⟨58688088687599433877169159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156501569833598490339117757 58688088687599433877169159)
      ·
        refine ⟨88032133031399150815753739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58688088687599433877169159 88032133031399150815753739)
        ·
          refine ⟨132048199547098726223630609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88032133031399150815753739 132048199547098726223630609)
          ·
            refine ⟨99036149660324044667722957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132048199547098726223630609 99036149660324044667722957)
            ·
              refine ⟨37138556122621516750396109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99036149660324044667722957 37138556122621516750396109)
              ·
                refine ⟨13926958545983068781398541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37138556122621516750396109 13926958545983068781398541)
                ·
                  refine ⟨5222609454743650793024453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13926958545983068781398541 5222609454743650793024453)
                  ·
                    refine ⟨979239272764434523692085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5222609454743650793024453 979239272764434523692085)
                    ·
                      rfl

theorem cell23_5721185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_5721185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721185 prefixEnd_5721185 := by exact prefixLift 5721185
  have htrace : WordTrace (prefixWord ++ tailWord_5721185) baseStart_5721185 baseEnd_5721185 := by
    simpa [prefixWord, tailWord_5721185, baseEnd_5721185] using wordTrace_append hprefix tailTrace_5721185
  have hstable : (prefixWord ++ tailWord_5721185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721185).length < 2 ^ (prefixWord ++ tailWord_5721185).sum := by decide
  have hdescent : baseEnd_5721185 < baseStart_5721185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721188 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_5721188 : Nat := 118140960795 + 5721188 * 2 ^ 59
def prefixEnd_5721188 : Nat := 4983230072969 + 3 ^ 40 * 5721188 * 2
def baseEnd_5721188 : Nat := 2937719358735267059338741

theorem tailTrace_5721188 : CollatzResearch.WordTrace tailWord_5721188 prefixEnd_5721188 2937719358735267059338741 := by
  unfold tailWord_5721188
  simp only [CollatzResearch.WordTrace]
  refine ⟨104334434598560225982258109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139112579464746967976344145 104334434598560225982258109)
  ·
    refine ⟨39125412974460084743346791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104334434598560225982258109 39125412974460084743346791)
    ·
      refine ⟨58688119461690127115020187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39125412974460084743346791 58688119461690127115020187)
      ·
        refine ⟨88032179192535190672530281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58688119461690127115020187 88032179192535190672530281)
        ·
          refine ⟨66024134394401393004397711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88032179192535190672530281 66024134394401393004397711)
          ·
            refine ⟨99036201591602089506596567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66024134394401393004397711 99036201591602089506596567)
            ·
              refine ⟨148554302387403134259894851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99036201591602089506596567 148554302387403134259894851)
              ·
                refine ⟨222831453581104701389842277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148554302387403134259894851 222831453581104701389842277)
                ·
                  refine ⟨41780897546457131510595427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222831453581104701389842277 41780897546457131510595427)
                  ·
                    refine ⟨62671346319685697265893141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41780897546457131510595427 62671346319685697265893141)
                    ·
                      refine ⟨2937719358735267059338741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62671346319685697265893141 2937719358735267059338741)
                      ·
                        rfl

theorem cell23_5721188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_5721188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721188 prefixEnd_5721188 := by exact prefixLift 5721188
  have htrace : WordTrace (prefixWord ++ tailWord_5721188) baseStart_5721188 baseEnd_5721188 := by
    simpa [prefixWord, tailWord_5721188, baseEnd_5721188] using wordTrace_append hprefix tailTrace_5721188
  have hstable : (prefixWord ++ tailWord_5721188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721188).length < 2 ^ (prefixWord ++ tailWord_5721188).sum := by decide
  have hdescent : baseEnd_5721188 < baseStart_5721188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721245 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_5721245 : Nat := 118140960795 + 5721245 * 2 ^ 59
def prefixEnd_5721245 : Nat := 4983230072969 + 3 ^ 40 * 5721245 * 2
def baseEnd_5721245 : Nat := 979249542377524445441993

theorem tailTrace_5721245 : CollatzResearch.WordTrace tailWord_5721245 prefixEnd_5721245 979249542377524445441993 := by
  unfold tailWord_5721245
  simp only [CollatzResearch.WordTrace]
  refine ⟨208670948157913950699341189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139113965438609300466227459 208670948157913950699341189)
  ·
    refine ⟨39125802779608865756126473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208670948157913950699341189 39125802779608865756126473)
    ·
      refine ⟨29344352084706649317094855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39125802779608865756126473 29344352084706649317094855)
      ·
        refine ⟨44016528127059973975642283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29344352084706649317094855 44016528127059973975642283)
        ·
          refine ⟨66024792190589960963463425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44016528127059973975642283 66024792190589960963463425)
          ·
            refine ⟨49518594142942470722597569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66024792190589960963463425 49518594142942470722597569)
            ·
              refine ⟨37138945607206853041948177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49518594142942470722597569 37138945607206853041948177)
              ·
                refine ⟨27854209205405139781461133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37138945607206853041948177 27854209205405139781461133)
                ·
                  refine ⟨10445328452026927418047925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27854209205405139781461133 10445328452026927418047925)
                  ·
                    refine ⟨979249542377524445441993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10445328452026927418047925 979249542377524445441993)
                    ·
                      rfl

theorem cell23_5721245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_5721245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721245 prefixEnd_5721245 := by exact prefixLift 5721245
  have htrace : WordTrace (prefixWord ++ tailWord_5721245) baseStart_5721245 baseEnd_5721245 := by
    simpa [prefixWord, tailWord_5721245, baseEnd_5721245] using wordTrace_append hprefix tailTrace_5721245
  have hstable : (prefixWord ++ tailWord_5721245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721245).length < 2 ^ (prefixWord ++ tailWord_5721245).sum := by decide
  have hdescent : baseEnd_5721245 < baseStart_5721245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721275 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 4, 4]
def baseStart_5721275 : Nat := 118140960795 + 5721275 * 2 ^ 59
def prefixEnd_5721275 : Nat := 4983230072969 + 3 ^ 40 * 5721275 * 2
def baseEnd_5721275 : Nat := 979254677184069406316947

theorem tailTrace_5721275 : CollatzResearch.WordTrace tailWord_5721275 prefixEnd_5721275 979254677184069406316947 := by
  unfold tailWord_5721275
  simp only [CollatzResearch.WordTrace]
  refine ⟨208672042347805265822933279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139114694898536843881955519 208672042347805265822933279)
  ·
    refine ⟨313008063521707898734399919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208672042347805265822933279 313008063521707898734399919)
    ·
      refine ⟨469512095282561848101599879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313008063521707898734399919 469512095282561848101599879)
      ·
        refine ⟨704268142923842772152399819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469512095282561848101599879 704268142923842772152399819)
        ·
          refine ⟨1056402214385764158228599729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704268142923842772152399819 1056402214385764158228599729)
          ·
            refine ⟨792301660789323118671449797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056402214385764158228599729 792301660789323118671449797)
            ·
              refine ⟨148556561397998084750896837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 792301660789323118671449797 148556561397998084750896837)
              ·
                refine ⟨27854355262124640890793157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148556561397998084750896837 27854355262124640890793157)
                ·
                  refine ⟨5222691611648370167023717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27854355262124640890793157 5222691611648370167023717)
                  ·
                    refine ⟨979254677184069406316947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5222691611648370167023717 979254677184069406316947)
                    ·
                      rfl

theorem cell23_5721275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 4].length) (baseStart_5721275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721275 prefixEnd_5721275 := by exact prefixLift 5721275
  have htrace : WordTrace (prefixWord ++ tailWord_5721275) baseStart_5721275 baseEnd_5721275 := by
    simpa [prefixWord, tailWord_5721275, baseEnd_5721275] using wordTrace_append hprefix tailTrace_5721275
  have hstable : (prefixWord ++ tailWord_5721275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721275).length < 2 ^ (prefixWord ++ tailWord_5721275).sum := by decide
  have hdescent : baseEnd_5721275 < baseStart_5721275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721309 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_5721309 : Nat := 118140960795 + 5721309 * 2 ^ 59
def prefixEnd_5721309 : Nat := 4983230072969 + 3 ^ 40 * 5721309 * 2
def baseEnd_5721309 : Nat := 979260496631487028641895

theorem tailTrace_5721309 : CollatzResearch.WordTrace tailWord_5721309 prefixEnd_5721309 979260496631487028641895 := by
  unfold tailWord_5721309
  simp only [CollatzResearch.WordTrace]
  refine ⟨208673282429682089629670981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139115521619788059753113987 208673282429682089629670981)
  ·
    refine ⟨39126240455565391805563309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208673282429682089629670981 39126240455565391805563309)
    ·
      refine ⟨14672340170837021927086241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39126240455565391805563309 14672340170837021927086241)
      ·
        refine ⟨11004255128127766445314681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14672340170837021927086241 11004255128127766445314681)
        ·
          refine ⟨8253191346095824833986011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11004255128127766445314681 8253191346095824833986011)
          ·
            refine ⟨12379787019143737250979017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8253191346095824833986011 12379787019143737250979017)
            ·
              refine ⟨9284840264357802938234263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12379787019143737250979017 9284840264357802938234263)
              ·
                refine ⟨13927260396536704407351395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9284840264357802938234263 13927260396536704407351395)
                ·
                  refine ⟨20890890594805056611027093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13927260396536704407351395 20890890594805056611027093)
                  ·
                    refine ⟨979260496631487028641895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20890890594805056611027093 979260496631487028641895)
                    ·
                      rfl

theorem cell23_5721309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_5721309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721309 prefixEnd_5721309 := by exact prefixLift 5721309
  have htrace : WordTrace (prefixWord ++ tailWord_5721309) baseStart_5721309 baseEnd_5721309 := by
    simpa [prefixWord, tailWord_5721309, baseEnd_5721309] using wordTrace_append hprefix tailTrace_5721309
  have hstable : (prefixWord ++ tailWord_5721309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721309).length < 2 ^ (prefixWord ++ tailWord_5721309).sum := by decide
  have hdescent : baseEnd_5721309 < baseStart_5721309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721312 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_5721312 : Nat := 118140960795 + 5721312 * 2 ^ 59
def prefixEnd_5721312 : Nat := 4983230072969 + 3 ^ 40 * 5721312 * 2
def baseEnd_5721312 : Nat := 2937783030336424574188171

theorem tailTrace_5721312 : CollatzResearch.WordTrace tailWord_5721312 prefixEnd_5721312 2937783030336424574188171 := by
  unfold tailWord_5721312
  simp only [CollatzResearch.WordTrace]
  refine ⟨104336695924335610571015095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139115594565780814094686793 104336695924335610571015095)
  ·
    refine ⟨156505043886503415856522643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104336695924335610571015095 156505043886503415856522643)
    ·
      refine ⟨234757565829755123784783965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156505043886503415856522643 234757565829755123784783965)
      ·
        refine ⟨88034087186158171419293987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234757565829755123784783965 88034087186158171419293987)
        ·
          refine ⟨132051130779237257128940981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88034087186158171419293987 132051130779237257128940981)
          ·
            refine ⟨12379793510553492855838217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132051130779237257128940981 12379793510553492855838217)
            ·
              refine ⟨9284845132915119641878663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12379793510553492855838217 9284845132915119641878663)
              ·
                refine ⟨13927267699372679462817995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9284845132915119641878663 13927267699372679462817995)
                ·
                  refine ⟨20890901549059019194226993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13927267699372679462817995 20890901549059019194226993)
                  ·
                    refine ⟨15668176161794264395670245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20890901549059019194226993 15668176161794264395670245)
                    ·
                      refine ⟨2937783030336424574188171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15668176161794264395670245 2937783030336424574188171)
                      ·
                        rfl

theorem cell23_5721312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_5721312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721312 prefixEnd_5721312 := by exact prefixLift 5721312
  have htrace : WordTrace (prefixWord ++ tailWord_5721312) baseStart_5721312 baseEnd_5721312 := by
    simpa [prefixWord, tailWord_5721312, baseEnd_5721312] using wordTrace_append hprefix tailTrace_5721312
  have hstable : (prefixWord ++ tailWord_5721312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721312).length < 2 ^ (prefixWord ++ tailWord_5721312).sum := by decide
  have hdescent : baseEnd_5721312 < baseStart_5721312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721322 : List Nat := [3, 1, 3, 1, 1, 4, 3, 7]
def baseStart_5721322 : Nat := 118140960795 + 5721322 * 2 ^ 59
def prefixEnd_5721322 : Nat := 4983230072969 + 3 ^ 40 * 5721322 * 2
def baseEnd_5721322 : Nat := 108806969079369242039375

theorem tailTrace_5721322 : CollatzResearch.WordTrace tailWord_5721322 prefixEnd_5721322 108806969079369242039375 := by
  unfold tailWord_5721322
  simp only [CollatzResearch.WordTrace]
  refine ⟨52168439144658748212473555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139115837719089995233262813 52168439144658748212473555)
  ·
    refine ⟨78252658716988122318710333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52168439144658748212473555 78252658716988122318710333)
    ·
      refine ⟨29344747018870545869516375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78252658716988122318710333 29344747018870545869516375)
      ·
        refine ⟨44017120528305818804274563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29344747018870545869516375 44017120528305818804274563)
        ·
          refine ⟨66025680792458728206411845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44017120528305818804274563 66025680792458728206411845)
          ·
            refine ⟨12379815148586011538702221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66025680792458728206411845 12379815148586011538702221)
            ·
              refine ⟨4642430680719754327013333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12379815148586011538702221 4642430680719754327013333)
              ·
                refine ⟨108806969079369242039375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4642430680719754327013333 108806969079369242039375)
                ·
                  rfl

theorem cell23_5721322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_5721322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721322 prefixEnd_5721322 := by exact prefixLift 5721322
  have htrace : WordTrace (prefixWord ++ tailWord_5721322) baseStart_5721322 baseEnd_5721322 := by
    simpa [prefixWord, tailWord_5721322, baseEnd_5721322] using wordTrace_append hprefix tailTrace_5721322
  have hstable : (prefixWord ++ tailWord_5721322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721322).length < 2 ^ (prefixWord ++ tailWord_5721322).sum := by decide
  have hdescent : baseEnd_5721322 < baseStart_5721322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721406 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_5721406 : Nat := 118140960795 + 5721406 * 2 ^ 59
def prefixEnd_5721406 : Nat := 4983230072969 + 3 ^ 40 * 5721406 * 2
def baseEnd_5721406 : Nat := 2937831297517947206412739

theorem tailTrace_5721406 : CollatzResearch.WordTrace tailWord_5721406 prefixEnd_5721406 2937831297517947206412739 := by
  unfold tailWord_5721406
  simp only [CollatzResearch.WordTrace]
  refine ⟨26084602538791334399494009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139117880206887116797301381 26084602538791334399494009)
  ·
    refine ⟨19563451904093500799620507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26084602538791334399494009 19563451904093500799620507)
    ·
      refine ⟨29345177856140251199430761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19563451904093500799620507 29345177856140251199430761)
      ·
        refine ⟨22008883392105188399573071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29345177856140251199430761 22008883392105188399573071)
        ·
          refine ⟨33013325088157782599359607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22008883392105188399573071 33013325088157782599359607)
          ·
            refine ⟨49519987632236673899039411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33013325088157782599359607 49519987632236673899039411)
            ·
              refine ⟨74279981448355010848559117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49519987632236673899039411 74279981448355010848559117)
              ·
                refine ⟨27854993043133129068209669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74279981448355010848559117 27854993043133129068209669)
                ·
                  refine ⟨5222811195587461700289313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27854993043133129068209669 5222811195587461700289313)
                  ·
                    refine ⟨3917108396690596275216985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5222811195587461700289313 3917108396690596275216985)
                    ·
                      refine ⟨2937831297517947206412739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917108396690596275216985 2937831297517947206412739)
                      ·
                        rfl

theorem cell23_5721406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_5721406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721406 prefixEnd_5721406 := by exact prefixLift 5721406
  have htrace : WordTrace (prefixWord ++ tailWord_5721406) baseStart_5721406 baseEnd_5721406 := by
    simpa [prefixWord, tailWord_5721406, baseEnd_5721406] using wordTrace_append hprefix tailTrace_5721406
  have hstable : (prefixWord ++ tailWord_5721406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721406).length < 2 ^ (prefixWord ++ tailWord_5721406).sum := by decide
  have hdescent : baseEnd_5721406 < baseStart_5721406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721422 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_5721422 : Nat := 118140960795 + 5721422 * 2 ^ 59
def prefixEnd_5721422 : Nat := 4983230072969 + 3 ^ 40 * 5721422 * 2
def baseEnd_5721422 : Nat := 2937839513208419143812665

theorem tailTrace_5721422 : CollatzResearch.WordTrace tailWord_5721422 prefixEnd_5721422 2937839513208419143812665 := by
  unfold tailWord_5721422
  simp only [CollatzResearch.WordTrace]
  refine ⟨26084675484784088741066815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139118269252181806619023013 26084675484784088741066815)
  ·
    refine ⟨39127013227176133111600223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26084675484784088741066815 39127013227176133111600223)
    ·
      refine ⟨58690519840764199667400335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39127013227176133111600223 58690519840764199667400335)
      ·
        refine ⟨88035779761146299501100503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58690519840764199667400335 88035779761146299501100503)
        ·
          refine ⟨132053669641719449251650755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88035779761146299501100503 132053669641719449251650755)
          ·
            refine ⟨198080504462579173877476133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132053669641719449251650755 198080504462579173877476133)
            ·
              refine ⟨37140094586733595102026775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198080504462579173877476133 37140094586733595102026775)
              ·
                refine ⟨55710141880100392653040163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37140094586733595102026775 55710141880100392653040163)
                ·
                  refine ⟨83565212820150588979560245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55710141880100392653040163 83565212820150588979560245)
                  ·
                    refine ⟨7834238701889117716833773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83565212820150588979560245 7834238701889117716833773)
                    ·
                      refine ⟨2937839513208419143812665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7834238701889117716833773 2937839513208419143812665)
                      ·
                        rfl

theorem cell23_5721422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_5721422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721422 prefixEnd_5721422 := by exact prefixLift 5721422
  have htrace : WordTrace (prefixWord ++ tailWord_5721422) baseStart_5721422 baseEnd_5721422 := by
    simpa [prefixWord, tailWord_5721422, baseEnd_5721422] using wordTrace_append hprefix tailTrace_5721422
  have hstable : (prefixWord ++ tailWord_5721422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721422).length < 2 ^ (prefixWord ++ tailWord_5721422).sum := by decide
  have hdescent : baseEnd_5721422 < baseStart_5721422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721452 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_5721452 : Nat := 118140960795 + 5721452 * 2 ^ 59
def prefixEnd_5721452 : Nat := 4983230072969 + 3 ^ 40 * 5721452 * 2
def baseEnd_5721452 : Nat := 2937854917628054026437527

theorem tailTrace_5721452 : CollatzResearch.WordTrace tailWord_5721452 prefixEnd_5721452 2937854917628054026437527 := by
  unfold tailWord_5721452
  simp only [CollatzResearch.WordTrace]
  refine ⟨104339249034082012526063305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139118998712109350034751073 104339249034082012526063305)
  ·
    refine ⟨78254436775561509394547479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104339249034082012526063305 78254436775561509394547479)
    ·
      refine ⟨117381655163342264091821219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78254436775561509394547479 117381655163342264091821219)
      ·
        refine ⟨176072482745013396137731829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117381655163342264091821219 176072482745013396137731829)
        ·
          refine ⟨16506795257345005887912359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176072482745013396137731829 16506795257345005887912359)
          ·
            refine ⟨24760192886017508831868539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16506795257345005887912359 24760192886017508831868539)
            ·
              refine ⟨37140289329026263247802809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24760192886017508831868539 37140289329026263247802809)
              ·
                refine ⟨27855216996769697435852107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37140289329026263247802809 27855216996769697435852107)
                ·
                  refine ⟨41782825495154546153778161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27855216996769697435852107 41782825495154546153778161)
                  ·
                    refine ⟨31337119121365909615333621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41782825495154546153778161 31337119121365909615333621)
                    ·
                      refine ⟨2937854917628054026437527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31337119121365909615333621 2937854917628054026437527)
                      ·
                        rfl

theorem cell23_5721452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_5721452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721452 prefixEnd_5721452 := by exact prefixLift 5721452
  have htrace : WordTrace (prefixWord ++ tailWord_5721452) baseStart_5721452 baseEnd_5721452 := by
    simpa [prefixWord, tailWord_5721452, baseEnd_5721452] using wordTrace_append hprefix tailTrace_5721452
  have hstable : (prefixWord ++ tailWord_5721452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721452).length < 2 ^ (prefixWord ++ tailWord_5721452).sum := by decide
  have hdescent : baseEnd_5721452 < baseStart_5721452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721472 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 7, 4]
def baseStart_5721472 : Nat := 118140960795 + 5721472 * 2 ^ 59
def prefixEnd_5721472 : Nat := 4983230072969 + 3 ^ 40 * 5721472 * 2
def baseEnd_5721472 : Nat := 979288395747047982729145

theorem tailTrace_5721472 : CollatzResearch.WordTrace tailWord_5721472 prefixEnd_5721472 979288395747047982729145 := by
  unfold tailWord_5721472
  simp only [CollatzResearch.WordTrace]
  refine ⟨104339613764045784233927335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139119485018727712311903113 104339613764045784233927335)
  ·
    refine ⟨156509420646068676350891003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104339613764045784233927335 156509420646068676350891003)
    ·
      refine ⟨234764130969103014526336505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156509420646068676350891003 234764130969103014526336505)
      ·
        refine ⟨176073098226827260894752379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234764130969103014526336505 176073098226827260894752379)
        ·
          refine ⟨264109647340240891342128569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176073098226827260894752379 264109647340240891342128569)
          ·
            refine ⟨198082235505180668506596427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264109647340240891342128569 198082235505180668506596427)
            ·
              refine ⟨297123353257771002759894641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198082235505180668506596427 297123353257771002759894641)
              ·
                refine ⟨222842514943328252069920981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297123353257771002759894641 222842514943328252069920981)
                ·
                  refine ⟨5222871443984255907888773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 222842514943328252069920981 5222871443984255907888773)
                  ·
                    refine ⟨979288395747047982729145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5222871443984255907888773 979288395747047982729145)
                    ·
                      rfl

theorem cell23_5721472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_5721472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721472 prefixEnd_5721472 := by exact prefixLift 5721472
  have htrace : WordTrace (prefixWord ++ tailWord_5721472) baseStart_5721472 baseEnd_5721472 := by
    simpa [prefixWord, tailWord_5721472, baseEnd_5721472] using wordTrace_append hprefix tailTrace_5721472
  have hstable : (prefixWord ++ tailWord_5721472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721472).length < 2 ^ (prefixWord ++ tailWord_5721472).sum := by decide
  have hdescent : baseEnd_5721472 < baseStart_5721472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721479 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_5721479 : Nat := 118140960795 + 5721479 * 2 ^ 59
def prefixEnd_5721479 : Nat := 4983230072969 + 3 ^ 40 * 5721479 * 2
def baseEnd_5721479 : Nat := 2937868781605725420799903

theorem tailTrace_5721479 : CollatzResearch.WordTrace tailWord_5721479 prefixEnd_5721479 2937868781605725420799903 := by
  unfold tailWord_5721479
  simp only [CollatzResearch.WordTrace]
  refine ⟨208679482839066208663359491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139119655226044139108906327 208679482839066208663359491)
  ·
    refine ⟨313019224258599312995039237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208679482839066208663359491 313019224258599312995039237)
    ·
      refine ⟨58691104548487371186569857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313019224258599312995039237 58691104548487371186569857)
      ·
        refine ⟨44018328411365528389927393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58691104548487371186569857 44018328411365528389927393)
        ·
          refine ⟨33013746308524146292445545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44018328411365528389927393 33013746308524146292445545)
          ·
            refine ⟨24760309731393109719334159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33013746308524146292445545 24760309731393109719334159)
            ·
              refine ⟨37140464597089664579001239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24760309731393109719334159 37140464597089664579001239)
              ·
                refine ⟨55710696895634496868501859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37140464597089664579001239 55710696895634496868501859)
                ·
                  refine ⟨83566045343451745302752789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55710696895634496868501859 83566045343451745302752789)
                  ·
                    refine ⟨3917158375474300561066537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83566045343451745302752789 3917158375474300561066537)
                    ·
                      refine ⟨2937868781605725420799903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917158375474300561066537 2937868781605725420799903)
                      ·
                        rfl

theorem cell23_5721479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_5721479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721479 prefixEnd_5721479 := by exact prefixLift 5721479
  have htrace : WordTrace (prefixWord ++ tailWord_5721479) baseStart_5721479 baseEnd_5721479 := by
    simpa [prefixWord, tailWord_5721479, baseEnd_5721479] using wordTrace_append hprefix tailTrace_5721479
  have hstable : (prefixWord ++ tailWord_5721479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721479).length < 2 ^ (prefixWord ++ tailWord_5721479).sum := by decide
  have hdescent : baseEnd_5721479 < baseStart_5721479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721539 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 1, 5, 2]
def baseStart_5721539 : Nat := 118140960795 + 5721539 * 2 ^ 59
def prefixEnd_5721539 : Nat := 4983230072969 + 3 ^ 40 * 5721539 * 2
def baseEnd_5721539 : Nat := 2937899590444995186049627

theorem tailTrace_5721539 : CollatzResearch.WordTrace tailWord_5721539 prefixEnd_5721539 2937899590444995186049627 := by
  unfold tailWord_5721539
  simp only [CollatzResearch.WordTrace]
  refine ⟨208681671218848838910543671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139121114145899225940362447 208681671218848838910543671)
  ·
    refine ⟨313022506828273258365815507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208681671218848838910543671 313022506828273258365815507)
    ·
      refine ⟨469533760242409887548723261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313022506828273258365815507 469533760242409887548723261)
      ·
        refine ⟨176075160090903707830771223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469533760242409887548723261 176075160090903707830771223)
        ·
          refine ⟨264112740136355561746156835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176075160090903707830771223 264112740136355561746156835)
          ·
            refine ⟨396169110204533342619235253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264112740136355561746156835 396169110204533342619235253)
            ·
              refine ⟨37140854081675000870553305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 396169110204533342619235253 37140854081675000870553305)
              ·
                refine ⟨27855640561256250652914979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37140854081675000870553305 27855640561256250652914979)
                ·
                  refine ⟨41783460841884375979372469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27855640561256250652914979 41783460841884375979372469)
                  ·
                    refine ⟨3917199453926660248066169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41783460841884375979372469 3917199453926660248066169)
                    ·
                      refine ⟨2937899590444995186049627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917199453926660248066169 2937899590444995186049627)
                      ·
                        rfl

theorem cell23_5721539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_5721539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721539 prefixEnd_5721539 := by exact prefixLift 5721539
  have htrace : WordTrace (prefixWord ++ tailWord_5721539) baseStart_5721539 baseEnd_5721539 := by
    simpa [prefixWord, tailWord_5721539, baseEnd_5721539] using wordTrace_append hprefix tailTrace_5721539
  have hstable : (prefixWord ++ tailWord_5721539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721539).length < 2 ^ (prefixWord ++ tailWord_5721539).sum := by decide
  have hdescent : baseEnd_5721539 < baseStart_5721539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721546 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_5721546 : Nat := 118140960795 + 5721546 * 2 ^ 59
def prefixEnd_5721546 : Nat := 4983230072969 + 3 ^ 40 * 5721546 * 2
def baseEnd_5721546 : Nat := 2937903184809576658662095

theorem tailTrace_5721546 : CollatzResearch.WordTrace tailWord_5721546 prefixEnd_5721546 2937903184809576658662095 := by
  unfold tailWord_5721546
  simp only [CollatzResearch.WordTrace]
  refine ⟨52170481632455869776512123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139121284353215652737365661 52170481632455869776512123)
  ·
    refine ⟨78255722448683804664768185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52170481632455869776512123 78255722448683804664768185)
    ·
      refine ⟨58691791836512853498576139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78255722448683804664768185 58691791836512853498576139)
      ·
        refine ⟨88037687754769280247864209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58691791836512853498576139 88037687754769280247864209)
        ·
          refine ⟨66028265816076960185898157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88037687754769280247864209 66028265816076960185898157)
          ·
            refine ⟨24760599681028860069711809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66028265816076960185898157 24760599681028860069711809)
            ·
              refine ⟨18570449760771645052283857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24760599681028860069711809 18570449760771645052283857)
              ·
                refine ⟨13927837320578733789212893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18570449760771645052283857 13927837320578733789212893)
                ·
                  refine ⟨5222938995217025170954835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13927837320578733789212893 5222938995217025170954835)
                  ·
                    refine ⟨7834408492825537756432253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5222938995217025170954835 7834408492825537756432253)
                    ·
                      refine ⟨2937903184809576658662095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7834408492825537756432253 2937903184809576658662095)
                      ·
                        rfl

theorem cell23_5721546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_5721546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721546 prefixEnd_5721546 := by exact prefixLift 5721546
  have htrace : WordTrace (prefixWord ++ tailWord_5721546) baseStart_5721546 baseEnd_5721546 := by
    simpa [prefixWord, tailWord_5721546, baseEnd_5721546] using wordTrace_append hprefix tailTrace_5721546
  have hstable : (prefixWord ++ tailWord_5721546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721546).length < 2 ^ (prefixWord ++ tailWord_5721546).sum := by decide
  have hdescent : baseEnd_5721546 < baseStart_5721546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721573 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5721573 : Nat := 118140960795 + 5721573 * 2 ^ 59
def prefixEnd_5721573 : Nat := 4983230072969 + 3 ^ 40 * 5721573 * 2
def baseEnd_5721573 : Nat := 2937917048787248053024471

theorem tailTrace_5721573 : CollatzResearch.WordTrace tailWord_5721573 prefixEnd_5721573 2937917048787248053024471 := by
  unfold tailWord_5721573
  simp only [CollatzResearch.WordTrace]
  refine ⟨208682911300725662717281373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139121940867150441811520915 208682911300725662717281373)
  ·
    refine ⟨78256091737772123518980515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208682911300725662717281373 78256091737772123518980515)
    ·
      refine ⟨117384137606658185278470773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78256091737772123518980515 117384137606658185278470773)
      ·
        refine ⟨11004762900624204869856635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117384137606658185278470773 11004762900624204869856635)
        ·
          refine ⟨16507144350936307304784953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11004762900624204869856635 16507144350936307304784953)
          ·
            refine ⟨12380358263202230478588715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16507144350936307304784953 12380358263202230478588715)
            ·
              refine ⟨18570537394803345717883073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12380358263202230478588715 18570537394803345717883073)
              ·
                refine ⟨13927903046102509288412305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18570537394803345717883073 13927903046102509288412305)
                ·
                  refine ⟨10445927284576881966309229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13927903046102509288412305 10445927284576881966309229)
                  ·
                    refine ⟨3917222731716330737365961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10445927284576881966309229 3917222731716330737365961)
                    ·
                      refine ⟨2937917048787248053024471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917222731716330737365961 2937917048787248053024471)
                      ·
                        rfl

theorem cell23_5721573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5721573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721573 prefixEnd_5721573 := by exact prefixLift 5721573
  have htrace : WordTrace (prefixWord ++ tailWord_5721573) baseStart_5721573 baseEnd_5721573 := by
    simpa [prefixWord, tailWord_5721573, baseEnd_5721573] using wordTrace_append hprefix tailTrace_5721573
  have hstable : (prefixWord ++ tailWord_5721573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721573).length < 2 ^ (prefixWord ++ tailWord_5721573).sum := by decide
  have hdescent : baseEnd_5721573 < baseStart_5721573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721592 : List Nat := [2, 1, 2, 1, 1, 5, 1, 10]
def baseStart_5721592 : Nat := 118140960795 + 5721592 * 2 ^ 59
def prefixEnd_5721592 : Nat := 4983230072969 + 3 ^ 40 * 5721592 * 2
def baseEnd_5721592 : Nat := 108812103885914202914329

theorem tailTrace_5721592 : CollatzResearch.WordTrace tailWord_5721592 prefixEnd_5721592 108812103885914202914329 := by
  unfold tailWord_5721592
  simp only [CollatzResearch.WordTrace]
  refine ⟨104341802143828414481111515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139122402858437885974815353 104341802143828414481111515)
  ·
    refine ⟨156512703215742621721667273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104341802143828414481111515 156512703215742621721667273)
    ·
      refine ⟨117384527411806966291250455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156512703215742621721667273 117384527411806966291250455)
      ·
        refine ⟨176076791117710449436875683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117384527411806966291250455 176076791117710449436875683)
        ·
          refine ⟨264115186676565674155313525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176076791117710449436875683 264115186676565674155313525)
          ·
            refine ⟨24760798750928031952060643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264115186676565674155313525 24760798750928031952060643)
            ·
              refine ⟨37141198126392047928090965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24760798750928031952060643 37141198126392047928090965)
              ·
                refine ⟨108812103885914202914329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37141198126392047928090965 108812103885914202914329)
                ·
                  rfl

theorem cell23_5721592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 10].length) (baseStart_5721592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721592 prefixEnd_5721592 := by exact prefixLift 5721592
  have htrace : WordTrace (prefixWord ++ tailWord_5721592) baseStart_5721592 baseEnd_5721592 := by
    simpa [prefixWord, tailWord_5721592, baseEnd_5721592] using wordTrace_append hprefix tailTrace_5721592
  have hstable : (prefixWord ++ tailWord_5721592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721592).length < 2 ^ (prefixWord ++ tailWord_5721592).sum := by decide
  have hdescent : baseEnd_5721592 < baseStart_5721592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721619 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 3]
def baseStart_5721619 : Nat := 118140960795 + 5721619 * 2 ^ 59
def prefixEnd_5721619 : Nat := 4983230072969 + 3 ^ 40 * 5721619 * 2
def baseEnd_5721619 : Nat := 2937940668897354873049259

theorem tailTrace_5721619 : CollatzResearch.WordTrace tailWord_5721619 prefixEnd_5721619 2937940668897354873049259 := by
  unfold tailWord_5721619
  simp only [CollatzResearch.WordTrace]
  refine ⟨208684589058559012573455911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139123059372372675048970607 208684589058559012573455911)
  ·
    refine ⟨313026883587838518860183867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208684589058559012573455911 313026883587838518860183867)
    ·
      refine ⟨469540325381757778290275801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313026883587838518860183867 469540325381757778290275801)
      ·
        refine ⟨352155244036318333717706851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469540325381757778290275801 352155244036318333717706851)
        ·
          refine ⟨528232866054477500576560277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352155244036318333717706851 528232866054477500576560277)
          ·
            refine ⟨24760915596303632839526263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 528232866054477500576560277 24760915596303632839526263)
            ·
              refine ⟨37141373394455449259289395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24760915596303632839526263 37141373394455449259289395)
              ·
                refine ⟨55712060091683173888934093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37141373394455449259289395 55712060091683173888934093)
                ·
                  refine ⟨20892022534381190208350285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55712060091683173888934093 20892022534381190208350285)
                  ·
                    refine ⟨7834508450392946328131357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20892022534381190208350285 7834508450392946328131357)
                    ·
                      refine ⟨2937940668897354873049259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7834508450392946328131357 2937940668897354873049259)
                      ·
                        rfl

theorem cell23_5721619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_5721619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721619 prefixEnd_5721619 := by exact prefixLift 5721619
  have htrace : WordTrace (prefixWord ++ tailWord_5721619) baseStart_5721619 baseEnd_5721619 := by
    simpa [prefixWord, tailWord_5721619, baseEnd_5721619] using wordTrace_append hprefix tailTrace_5721619
  have hstable : (prefixWord ++ tailWord_5721619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721619).length < 2 ^ (prefixWord ++ tailWord_5721619).sum := by decide
  have hdescent : baseEnd_5721619 < baseStart_5721619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721653 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_5721653 : Nat := 118140960795 + 5721653 * 2 ^ 59
def prefixEnd_5721653 : Nat := 4983230072969 + 3 ^ 40 * 5721653 * 2
def baseEnd_5721653 : Nat := 2937958127239607740024103

theorem tailTrace_5721653 : CollatzResearch.WordTrace tailWord_5721653 prefixEnd_5721653 2937958127239607740024103 := by
  unfold tailWord_5721653
  simp only [CollatzResearch.WordTrace]
  refine ⟨208685829140435836380193613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139123886093623890920129075 208685829140435836380193613)
  ·
    refine ⟨78257185927663438642572605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208685829140435836380193613 78257185927663438642572605)
    ·
      refine ⟨29346444722873789490964727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78257185927663438642572605 29346444722873789490964727)
      ·
        refine ⟨44019667084310684236447091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29346444722873789490964727 44019667084310684236447091)
        ·
          refine ⟨66029500626466026354670637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44019667084310684236447091 66029500626466026354670637)
          ·
            refine ⟨24761062734924759883001489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66029500626466026354670637 24761062734924759883001489)
            ·
              refine ⟨18570797051193569912251117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24761062734924759883001489 18570797051193569912251117)
              ·
                refine ⟨6964048894197588717094169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18570797051193569912251117 6964048894197588717094169)
                ·
                  refine ⟨5223036670648191537820627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6964048894197588717094169 5223036670648191537820627)
                  ·
                    refine ⟨7834555005972287306730941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5223036670648191537820627 7834555005972287306730941)
                    ·
                      refine ⟨2937958127239607740024103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7834555005972287306730941 2937958127239607740024103)
                      ·
                        rfl

theorem cell23_5721653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_5721653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721653 prefixEnd_5721653 := by exact prefixLift 5721653
  have htrace : WordTrace (prefixWord ++ tailWord_5721653) baseStart_5721653 baseEnd_5721653 := by
    simpa [prefixWord, tailWord_5721653, baseEnd_5721653] using wordTrace_append hprefix tailTrace_5721653
  have hstable : (prefixWord ++ tailWord_5721653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721653).length < 2 ^ (prefixWord ++ tailWord_5721653).sum := by decide
  have hdescent : baseEnd_5721653 < baseStart_5721653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721699 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 7]
def baseStart_5721699 : Nat := 118140960795 + 5721699 * 2 ^ 59
def prefixEnd_5721699 : Nat := 4983230072969 + 3 ^ 40 * 5721699 * 2
def baseEnd_5721699 : Nat := 326442416372190506672099

theorem tailTrace_5721699 : CollatzResearch.WordTrace tailWord_5721699 prefixEnd_5721699 326442416372190506672099 := by
  unfold tailWord_5721699
  simp only [CollatzResearch.WordTrace]
  refine ⟨208687506898269186236368151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139125004598846124157578767 208687506898269186236368151)
  ·
    refine ⟨313031260347403779354552227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208687506898269186236368151 313031260347403779354552227)
    ·
      refine ⟨469546890521105669031828341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313031260347403779354552227 469546890521105669031828341)
      ·
        refine ⟨44020020986353656471733907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 469546890521105669031828341 44020020986353656471733907)
        ·
          refine ⟨66030031479530484707600861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44020020986353656471733907 66030031479530484707600861)
          ·
            refine ⟨24761261804823931765350323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66030031479530484707600861 24761261804823931765350323)
            ·
              refine ⟨37141892707235897648025485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24761261804823931765350323 37141892707235897648025485)
              ·
                refine ⟨13928209765213461618009557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37141892707235897648025485 13928209765213461618009557)
                ·
                  refine ⟨326442416372190506672099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13928209765213461618009557 326442416372190506672099)
                  ·
                    rfl

theorem cell23_5721699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 7].length) (baseStart_5721699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721699 prefixEnd_5721699 := by exact prefixLift 5721699
  have htrace : WordTrace (prefixWord ++ tailWord_5721699) baseStart_5721699 baseEnd_5721699 := by
    simpa [prefixWord, tailWord_5721699, baseEnd_5721699] using wordTrace_append hprefix tailTrace_5721699
  have hstable : (prefixWord ++ tailWord_5721699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721699).length < 2 ^ (prefixWord ++ tailWord_5721699).sum := by decide
  have hdescent : baseEnd_5721699 < baseStart_5721699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721706 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5721706 : Nat := 118140960795 + 5721706 * 2 ^ 59
def prefixEnd_5721706 : Nat := 4983230072969 + 3 ^ 40 * 5721706 * 2
def baseEnd_5721706 : Nat := 2937985341714296032661359

theorem tailTrace_5721706 : CollatzResearch.WordTrace tailWord_5721706 prefixEnd_5721706 2937985341714296032661359 := by
  unfold tailWord_5721706
  simp only [CollatzResearch.WordTrace]
  refine ⟨52171940552310956607968243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139125174806162550954581981 52171940552310956607968243)
  ·
    refine ⟨78257910828466434911952365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52171940552310956607968243 78257910828466434911952365)
    ·
      refine ⟨29346716560674913091982137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78257910828466434911952365 29346716560674913091982137)
      ·
        refine ⟨22010037420506184818986603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29346716560674913091982137 22010037420506184818986603)
        ·
          refine ⟨33015056130759277228479905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22010037420506184818986603 33015056130759277228479905)
          ·
            refine ⟨24761292098069457921359929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33015056130759277228479905 24761292098069457921359929)
            ·
              refine ⟨18570969073552093441019947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24761292098069457921359929 18570969073552093441019947)
              ·
                refine ⟨27856453610328140161529921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18570969073552093441019947 27856453610328140161529921)
                ·
                  refine ⟨20892340207746105121147441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27856453610328140161529921 20892340207746105121147441)
                  ·
                    refine ⟨15669255155809578840860581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20892340207746105121147441 15669255155809578840860581)
                    ·
                      refine ⟨2937985341714296032661359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15669255155809578840860581 2937985341714296032661359)
                      ·
                        rfl

theorem cell23_5721706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5721706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721706 prefixEnd_5721706 := by exact prefixLift 5721706
  have htrace : WordTrace (prefixWord ++ tailWord_5721706) baseStart_5721706 baseEnd_5721706 := by
    simpa [prefixWord, tailWord_5721706, baseEnd_5721706] using wordTrace_append hprefix tailTrace_5721706
  have hstable : (prefixWord ++ tailWord_5721706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721706).length < 2 ^ (prefixWord ++ tailWord_5721706).sum := by decide
  have hdescent : baseEnd_5721706 < baseStart_5721706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721739 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5]
def baseStart_5721739 : Nat := 118140960795 + 5721739 * 2 ^ 59
def prefixEnd_5721739 : Nat := 4983230072969 + 3 ^ 40 * 5721739 * 2
def baseEnd_5721739 : Nat := 2938002286575894403548707

theorem tailTrace_5721739 : CollatzResearch.WordTrace tailWord_5721739 prefixEnd_5721739 2938002286575894403548707 := by
  unfold tailWord_5721739
  simp only [CollatzResearch.WordTrace]
  refine ⟨208688965818124273067824271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139125977212082848711882847 208688965818124273067824271)
  ·
    refine ⟨313033448727186409601736407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208688965818124273067824271 313033448727186409601736407)
    ·
      refine ⟨469550173090779614402604611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313033448727186409601736407 469550173090779614402604611)
      ·
        refine ⟨704325259636169421603906917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469550173090779614402604611 704325259636169421603906917)
        ·
          refine ⟨132060986181781766550732547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 704325259636169421603906917 132060986181781766550732547)
          ·
            refine ⟨198091479272672649826098821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132060986181781766550732547 198091479272672649826098821)
            ·
              refine ⟨37142152363626121842393529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198091479272672649826098821 37142152363626121842393529)
              ·
                refine ⟨27856614272719591381795147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37142152363626121842393529 27856614272719591381795147)
                ·
                  refine ⟨41784921409079387072692721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27856614272719591381795147 41784921409079387072692721)
                  ·
                    refine ⟨31338691056809540304519541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41784921409079387072692721 31338691056809540304519541)
                    ·
                      refine ⟨2938002286575894403548707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31338691056809540304519541 2938002286575894403548707)
                      ·
                        rfl

theorem cell23_5721739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_5721739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721739 prefixEnd_5721739 := by exact prefixLift 5721739
  have htrace : WordTrace (prefixWord ++ tailWord_5721739) baseStart_5721739 baseEnd_5721739 := by
    simpa [prefixWord, tailWord_5721739, baseEnd_5721739] using wordTrace_append hprefix tailTrace_5721739
  have hstable : (prefixWord ++ tailWord_5721739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721739).length < 2 ^ (prefixWord ++ tailWord_5721739).sum := by decide
  have hdescent : baseEnd_5721739 < baseStart_5721739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721776 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 3, 4]
def baseStart_5721776 : Nat := 118140960795 + 5721776 * 2 ^ 59
def prefixEnd_5721776 : Nat := 4983230072969 + 3 ^ 40 * 5721776 * 2
def baseEnd_5721776 : Nat := 979340428453370252928679

theorem tailTrace_5721776 : CollatzResearch.WordTrace tailWord_5721776 prefixEnd_5721776 979340428453370252928679 := by
  unfold tailWord_5721776
  simp only [CollatzResearch.WordTrace]
  refine ⟨104345157659495114193460591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139126876879326818924614121 104345157659495114193460591)
  ·
    refine ⟨156517736489242671290190887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104345157659495114193460591 156517736489242671290190887)
    ·
      refine ⟨234776604733864006935286331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156517736489242671290190887 234776604733864006935286331)
      ·
        refine ⟨352164907100796010402929497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234776604733864006935286331 352164907100796010402929497)
        ·
          refine ⟨264123680325597007802197123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352164907100796010402929497 264123680325597007802197123)
          ·
            refine ⟨396185520488395511703295685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264123680325597007802197123 396185520488395511703295685)
            ·
              refine ⟨74284785091574158444367941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 396185520488395511703295685 74284785091574158444367941)
              ·
                refine ⟨13928397204670154708318989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74284785091574158444367941 13928397204670154708318989)
                ·
                  refine ⟨5223148951751308015619621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13928397204670154708318989 5223148951751308015619621)
                  ·
                    refine ⟨979340428453370252928679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223148951751308015619621 979340428453370252928679)
                    ·
                      rfl

theorem cell23_5721776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_5721776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721776 prefixEnd_5721776 := by exact prefixLift 5721776
  have htrace : WordTrace (prefixWord ++ tailWord_5721776) baseStart_5721776 baseEnd_5721776 := by
    simpa [prefixWord, tailWord_5721776, baseEnd_5721776] using wordTrace_append hprefix tailTrace_5721776
  have hstable : (prefixWord ++ tailWord_5721776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721776).length < 2 ^ (prefixWord ++ tailWord_5721776).sum := by decide
  have hdescent : baseEnd_5721776 < baseStart_5721776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721783 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_5721783 : Nat := 118140960795 + 5721783 * 2 ^ 59
def prefixEnd_5721783 : Nat := 4983230072969 + 3 ^ 40 * 5721783 * 2
def baseEnd_5721783 : Nat := 2938024879724692231398505

theorem tailTrace_5721783 : CollatzResearch.WordTrace tailWord_5721783 prefixEnd_5721783 2938024879724692231398505 := by
  unfold tailWord_5721783
  simp only [CollatzResearch.WordTrace]
  refine ⟨208690570629964868582426003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139127047086643245721617335 208690570629964868582426003)
  ·
    refine ⟨313035855944947302873639005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208690570629964868582426003 313035855944947302873639005)
    ·
      refine ⟨117388445979355238577614627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313035855944947302873639005 117388445979355238577614627)
      ·
        refine ⟨176082668969032857866421941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117388445979355238577614627 176082668969032857866421941)
        ·
          refine ⟨16507750215846830424977057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176082668969032857866421941 16507750215846830424977057)
          ·
            refine ⟨12380812661885122818732793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16507750215846830424977057 12380812661885122818732793)
            ·
              refine ⟨9285609496413842114049595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12380812661885122818732793 9285609496413842114049595)
              ·
                refine ⟨13928414244620763171074393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9285609496413842114049595 13928414244620763171074393)
                ·
                  refine ⟨10446310683465572378305795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13928414244620763171074393 10446310683465572378305795)
                  ·
                    refine ⟨15669466025198358567458693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10446310683465572378305795 15669466025198358567458693)
                    ·
                      refine ⟨2938024879724692231398505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15669466025198358567458693 2938024879724692231398505)
                      ·
                        rfl

theorem cell23_5721783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_5721783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721783 prefixEnd_5721783 := by exact prefixLift 5721783
  have htrace : WordTrace (prefixWord ++ tailWord_5721783) baseStart_5721783 baseEnd_5721783 := by
    simpa [prefixWord, tailWord_5721783, baseEnd_5721783] using wordTrace_append hprefix tailTrace_5721783
  have hstable : (prefixWord ++ tailWord_5721783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721783).length < 2 ^ (prefixWord ++ tailWord_5721783).sum := by decide
  have hdescent : baseEnd_5721783 < baseStart_5721783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721796 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5721796 : Nat := 118140960795 + 5721796 * 2 ^ 59
def prefixEnd_5721796 : Nat := 4983230072969 + 3 ^ 40 * 5721796 * 2
def baseEnd_5721796 : Nat := 2938031554973200680535945

theorem tailTrace_5721796 : CollatzResearch.WordTrace tailWord_5721796 prefixEnd_5721796 2938031554973200680535945 := by
  unfold tailWord_5721796
  simp only [CollatzResearch.WordTrace]
  refine ⟨104345522389458885901324621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139127363185945181201766161 104345522389458885901324621)
  ·
    refine ⟨39129570896047082212996733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104345522389458885901324621 39129570896047082212996733)
    ·
      refine ⟨14673589086017655829873775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39129570896047082212996733 14673589086017655829873775)
      ·
        refine ⟨22010383629026483744810663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14673589086017655829873775 22010383629026483744810663)
        ·
          refine ⟨33015575443539725617215995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22010383629026483744810663 33015575443539725617215995)
          ·
            refine ⟨49523363165309588425823993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33015575443539725617215995 49523363165309588425823993)
            ·
              refine ⟨37142522373982191319367995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49523363165309588425823993 37142522373982191319367995)
              ·
                refine ⟨55713783560973286979051993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37142522373982191319367995 55713783560973286979051993)
                ·
                  refine ⟨41785337670729965234288995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55713783560973286979051993 41785337670729965234288995)
                  ·
                    refine ⟨62678006506094947851433493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41785337670729965234288995 62678006506094947851433493)
                    ·
                      refine ⟨2938031554973200680535945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62678006506094947851433493 2938031554973200680535945)
                      ·
                        rfl

theorem cell23_5721796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5721796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721796 prefixEnd_5721796 := by exact prefixLift 5721796
  have htrace : WordTrace (prefixWord ++ tailWord_5721796) baseStart_5721796 baseEnd_5721796 := by
    simpa [prefixWord, tailWord_5721796, baseEnd_5721796] using wordTrace_append hprefix tailTrace_5721796
  have hstable : (prefixWord ++ tailWord_5721796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721796).length < 2 ^ (prefixWord ++ tailWord_5721796).sum := by decide
  have hdescent : baseEnd_5721796 < baseStart_5721796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721836 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_5721836 : Nat := 118140960795 + 5721836 * 2 ^ 59
def prefixEnd_5721836 : Nat := 4983230072969 + 3 ^ 40 * 5721836 * 2
def baseEnd_5721836 : Nat := 979350698066460174678587

theorem tailTrace_5721836 : CollatzResearch.WordTrace tailWord_5721836 prefixEnd_5721836 979350698066460174678587 := by
  unfold tailWord_5721836
  simp only [CollatzResearch.WordTrace]
  refine ⟨104346251849386429317052681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139128335799181905756070241 104346251849386429317052681)
  ·
    refine ⟨78259688887039821987789511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104346251849386429317052681 78259688887039821987789511)
    ·
      refine ⟨117389533330559732981684267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78259688887039821987789511 117389533330559732981684267)
      ·
        refine ⟨176084299995839599472526401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117389533330559732981684267 176084299995839599472526401)
        ·
          refine ⟨132063224996879699604394801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176084299995839599472526401 132063224996879699604394801)
          ·
            refine ⟨99047418747659774703296101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132063224996879699604394801 99047418747659774703296101)
            ·
              refine ⟨18571391015186207756868019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99047418747659774703296101 18571391015186207756868019)
              ·
                refine ⟨27857086522779311635302029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18571391015186207756868019 27857086522779311635302029)
                ·
                  refine ⟨10446407446042241863238261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27857086522779311635302029 10446407446042241863238261)
                  ·
                    refine ⟨979350698066460174678587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10446407446042241863238261 979350698066460174678587)
                    ·
                      rfl

theorem cell23_5721836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_5721836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721836 prefixEnd_5721836 := by exact prefixLift 5721836
  have htrace : WordTrace (prefixWord ++ tailWord_5721836) baseStart_5721836 baseEnd_5721836 := by
    simpa [prefixWord, tailWord_5721836, baseEnd_5721836] using wordTrace_append hprefix tailTrace_5721836
  have hstable : (prefixWord ++ tailWord_5721836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721836).length < 2 ^ (prefixWord ++ tailWord_5721836).sum := by decide
  have hdescent : baseEnd_5721836 < baseStart_5721836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721844 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5721844 : Nat := 118140960795 + 5721844 * 2 ^ 59
def prefixEnd_5721844 : Nat := 4983230072969 + 3 ^ 40 * 5721844 * 2
def baseEnd_5721844 : Nat := 979352067348205497578575

theorem tailTrace_5721844 : CollatzResearch.WordTrace tailWord_5721844 prefixEnd_5721844 979352067348205497578575 := by
  unfold tailWord_5721844
  simp only [CollatzResearch.WordTrace]
  refine ⟨104346397741371938000198293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139128530321829250666931057 104346397741371938000198293)
  ·
    refine ⟨4891237394126809593759295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104346397741371938000198293 4891237394126809593759295)
    ·
      refine ⟨7336856091190214390638943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891237394126809593759295 7336856091190214390638943)
      ·
        refine ⟨11005284136785321585958415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7336856091190214390638943 11005284136785321585958415)
        ·
          refine ⟨16507926205177982378937623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005284136785321585958415 16507926205177982378937623)
          ·
            refine ⟨24761889307766973568406435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16507926205177982378937623 24761889307766973568406435)
            ·
              refine ⟨37142833961650460352609653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24761889307766973568406435 37142833961650460352609653)
              ·
                refine ⟨3482140683904730658057155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37142833961650460352609653 3482140683904730658057155)
                ·
                  refine ⟨5223211025857095987085733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482140683904730658057155 5223211025857095987085733)
                  ·
                    refine ⟨979352067348205497578575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223211025857095987085733 979352067348205497578575)
                    ·
                      rfl

theorem cell23_5721844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5721844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721844 prefixEnd_5721844 := by exact prefixLift 5721844
  have htrace : WordTrace (prefixWord ++ tailWord_5721844) baseStart_5721844 baseEnd_5721844 := by
    simpa [prefixWord, tailWord_5721844, baseEnd_5721844] using wordTrace_append hprefix tailTrace_5721844
  have hstable : (prefixWord ++ tailWord_5721844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721844).length < 2 ^ (prefixWord ++ tailWord_5721844).sum := by decide
  have hdescent : baseEnd_5721844 < baseStart_5721844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721890 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_5721890 : Nat := 118140960795 + 5721890 * 2 ^ 59
def prefixEnd_5721890 : Nat := 4983230072969 + 3 ^ 40 * 5721890 * 2
def baseEnd_5721890 : Nat := 2938079822154723312760513

theorem tailTrace_5721890 : CollatzResearch.WordTrace tailWord_5721890 prefixEnd_5721890 2938079822154723312760513 := by
  unfold tailWord_5721890
  simp only [CollatzResearch.WordTrace]
  refine ⟨52173618310144306464142781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139129648827051483904380749 52173618310144306464142781)
  ·
    refine ⟨19565106866304114924053543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52173618310144306464142781 19565106866304114924053543)
    ·
      refine ⟨29347660299456172386080315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19565106866304114924053543 29347660299456172386080315)
      ·
        refine ⟨44021490449184258579120473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29347660299456172386080315 44021490449184258579120473)
        ·
          refine ⟨33016117836888193934340355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44021490449184258579120473 33016117836888193934340355)
          ·
            refine ⟨49524176755332290901510533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33016117836888193934340355 49524176755332290901510533)
            ·
              refine ⟨9285783141624804544033225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49524176755332290901510533 9285783141624804544033225)
              ·
                refine ⟨6964337356218603408024919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9285783141624804544033225 6964337356218603408024919)
                ·
                  refine ⟨10446506034327905112037379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6964337356218603408024919 10446506034327905112037379)
                  ·
                    refine ⟨15669759051491857668056069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10446506034327905112037379 15669759051491857668056069)
                    ·
                      refine ⟨2938079822154723312760513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15669759051491857668056069 2938079822154723312760513)
                      ·
                        rfl

theorem cell23_5721890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_5721890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721890 prefixEnd_5721890 := by exact prefixLift 5721890
  have htrace : WordTrace (prefixWord ++ tailWord_5721890) baseStart_5721890 baseEnd_5721890 := by
    simpa [prefixWord, tailWord_5721890, baseEnd_5721890] using wordTrace_append hprefix tailTrace_5721890
  have hstable : (prefixWord ++ tailWord_5721890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721890).length < 2 ^ (prefixWord ++ tailWord_5721890).sum := by decide
  have hdescent : baseEnd_5721890 < baseStart_5721890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721910 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5721910 : Nat := 118140960795 + 5721910 * 2 ^ 59
def prefixEnd_5721910 : Nat := 4983230072969 + 3 ^ 40 * 5721910 * 2
def baseEnd_5721910 : Nat := 2938090091767813234510421

theorem tailTrace_5721910 : CollatzResearch.WordTrace tailWord_5721910 prefixEnd_5721910 2938090091767813234510421 := by
  unfold tailWord_5721910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043450168781548079518699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139130135133669846181532789 13043450168781548079518699)
  ·
    refine ⟨19565175253172322119278049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13043450168781548079518699 19565175253172322119278049)
    ·
      refine ⟨14673881439879241589458537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19565175253172322119278049 14673881439879241589458537)
      ·
        refine ⟨11005411079909431192093903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14673881439879241589458537 11005411079909431192093903)
        ·
          refine ⟨16508116619864146788140855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005411079909431192093903 16508116619864146788140855)
          ·
            refine ⟨24762174929796220182211283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16508116619864146788140855 24762174929796220182211283)
            ·
              refine ⟨37143262394694330273316925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24762174929796220182211283 37143262394694330273316925)
              ·
                refine ⟨13928723398010373852493847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37143262394694330273316925 13928723398010373852493847)
                ·
                  refine ⟨20893085097015560778740771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13928723398010373852493847 20893085097015560778740771)
                  ·
                    refine ⟨31339627645523341168111157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20893085097015560778740771 31339627645523341168111157)
                    ·
                      refine ⟨2938090091767813234510421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31339627645523341168111157 2938090091767813234510421)
                      ·
                        rfl

theorem cell23_5721910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5721910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721910 prefixEnd_5721910 := by exact prefixLift 5721910
  have htrace : WordTrace (prefixWord ++ tailWord_5721910) baseStart_5721910 baseEnd_5721910 := by
    simpa [prefixWord, tailWord_5721910, baseEnd_5721910] using wordTrace_append hprefix tailTrace_5721910
  have hstable : (prefixWord ++ tailWord_5721910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721910).length < 2 ^ (prefixWord ++ tailWord_5721910).sum := by decide
  have hdescent : baseEnd_5721910 < baseStart_5721910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721973 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5721973 : Nat := 118140960795 + 5721973 * 2 ^ 59
def prefixEnd_5721973 : Nat := 4983230072969 + 3 ^ 40 * 5721973 * 2
def baseEnd_5721973 : Nat := 979374147016348829340877

theorem tailTrace_5721973 : CollatzResearch.WordTrace tailWord_5721973 prefixEnd_5721973 979374147016348829340877 := by
  unfold tailWord_5721973
  simp only [CollatzResearch.WordTrace]
  refine ⟨208697500499276531031842573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139131666999517687354561715 208697500499276531031842573)
  ·
    refine ⟨78261562687228699136940965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208697500499276531031842573 78261562687228699136940965)
    ·
      refine ⟨14674043003855381088176431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78261562687228699136940965 14674043003855381088176431)
      ·
        refine ⟨22011064505783071632264647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14674043003855381088176431 22011064505783071632264647)
        ·
          refine ⟨33016596758674607448396971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22011064505783071632264647 33016596758674607448396971)
          ·
            refine ⟨49524895138011911172595457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33016596758674607448396971 49524895138011911172595457)
            ·
              refine ⟨37143671353508933379446593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49524895138011911172595457 37143671353508933379446593)
              ·
                refine ⟨27857753515131700034584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37143671353508933379446593 27857753515131700034584945)
                ·
                  refine ⟨20893315136348775025938709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27857753515131700034584945 20893315136348775025938709)
                  ·
                    refine ⟨979374147016348829340877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20893315136348775025938709 979374147016348829340877)
                    ·
                      rfl

theorem cell23_5721973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5721973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721973 prefixEnd_5721973 := by exact prefixLift 5721973
  have htrace : WordTrace (prefixWord ++ tailWord_5721973) baseStart_5721973 baseEnd_5721973 := by
    simpa [prefixWord, tailWord_5721973, baseEnd_5721973] using wordTrace_append hprefix tailTrace_5721973
  have hstable : (prefixWord ++ tailWord_5721973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721973).length < 2 ^ (prefixWord ++ tailWord_5721973).sum := by decide
  have hdescent : baseEnd_5721973 < baseStart_5721973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5721993 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_5721993 : Nat := 118140960795 + 5721993 * 2 ^ 59
def prefixEnd_5721993 : Nat := 4983230072969 + 3 ^ 40 * 5721993 * 2
def baseEnd_5721993 : Nat := 2938132710662136409772539

theorem tailTrace_5721993 : CollatzResearch.WordTrace tailWord_5721993 prefixEnd_5721993 2938132710662136409772539 := by
  unfold tailWord_5721993
  simp only [CollatzResearch.WordTrace]
  refine ⟨208698229959204074447570633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139132153306136049631713755 208698229959204074447570633)
  ·
    refine ⟨156523672469403055835677975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208698229959204074447570633 156523672469403055835677975)
    ·
      refine ⟨234785508704104583753516963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156523672469403055835677975 234785508704104583753516963)
      ·
        refine ⟨352178263056156875630275445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234785508704104583753516963 352178263056156875630275445)
        ·
          refine ⟨33016712161514707090338323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352178263056156875630275445 33016712161514707090338323)
          ·
            refine ⟨49525068242272060635507485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33016712161514707090338323 49525068242272060635507485)
            ·
              refine ⟨18571900590852022738315307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49525068242272060635507485 18571900590852022738315307)
              ·
                refine ⟨27857850886278034107472961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18571900590852022738315307 27857850886278034107472961)
                ·
                  refine ⟨20893388164708525580604721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27857850886278034107472961 20893388164708525580604721)
                  ·
                    refine ⟨15670041123531394185453541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20893388164708525580604721 15670041123531394185453541)
                    ·
                      refine ⟨2938132710662136409772539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15670041123531394185453541 2938132710662136409772539)
                      ·
                        rfl

theorem cell23_5721993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_5721993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5721993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5721993 prefixEnd_5721993 := by exact prefixLift 5721993
  have htrace : WordTrace (prefixWord ++ tailWord_5721993) baseStart_5721993 baseEnd_5721993 := by
    simpa [prefixWord, tailWord_5721993, baseEnd_5721993] using wordTrace_append hprefix tailTrace_5721993
  have hstable : (prefixWord ++ tailWord_5721993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5721993).length < 2 ^ (prefixWord ++ tailWord_5721993).sum := by decide
  have hdescent : baseEnd_5721993 < baseStart_5721993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5721993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722018 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_5722018 : Nat := 118140960795 + 5722018 * 2 ^ 59
def prefixEnd_5722018 : Nat := 4983230072969 + 3 ^ 40 * 5722018 * 2
def baseEnd_5722018 : Nat := 2938145547678498811959925

theorem tailTrace_5722018 : CollatzResearch.WordTrace tailWord_5722018 prefixEnd_5722018 2938145547678498811959925 := by
  unfold tailWord_5722018
  simp only [CollatzResearch.WordTrace]
  refine ⟨52174785446028375929307677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139132761189409002478153805 52174785446028375929307677)
  ·
    refine ⟨19565544542260640973490379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52174785446028375929307677 19565544542260640973490379)
    ·
      refine ⟨29348316813390961460235569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19565544542260640973490379 29348316813390961460235569)
      ·
        refine ⟨22011237610043221095176677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29348316813390961460235569 22011237610043221095176677)
        ·
          refine ⟨4127107051883103955345627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22011237610043221095176677 4127107051883103955345627)
          ·
            refine ⟨6190660577824655933018441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127107051883103955345627 6190660577824655933018441)
            ·
              refine ⟨4642995433368491949763831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6190660577824655933018441 4642995433368491949763831)
              ·
                refine ⟨6964493150052737924645747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642995433368491949763831 6964493150052737924645747)
                ·
                  refine ⟨10446739725079106886968621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6964493150052737924645747 10446739725079106886968621)
                  ·
                    refine ⟨3917527396904665082613233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10446739725079106886968621 3917527396904665082613233)
                    ·
                      refine ⟨2938145547678498811959925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917527396904665082613233 2938145547678498811959925)
                      ·
                        rfl

theorem cell23_5722018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_5722018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722018 prefixEnd_5722018 := by exact prefixLift 5722018
  have htrace : WordTrace (prefixWord ++ tailWord_5722018) baseStart_5722018 baseEnd_5722018 := by
    simpa [prefixWord, tailWord_5722018, baseEnd_5722018] using wordTrace_append hprefix tailTrace_5722018
  have hstable : (prefixWord ++ tailWord_5722018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722018).length < 2 ^ (prefixWord ++ tailWord_5722018).sum := by decide
  have hdescent : baseEnd_5722018 < baseStart_5722018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722020 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 5]
def baseStart_5722020 : Nat := 118140960795 + 5722020 * 2 ^ 59
def prefixEnd_5722020 : Nat := 4983230072969 + 3 ^ 40 * 5722020 * 2
def baseEnd_5722020 : Nat := 326460730515534200459435

theorem tailTrace_5722020 : CollatzResearch.WordTrace tailWord_5722020 prefixEnd_5722020 326460730515534200459435 := by
  unfold tailWord_5722020
  simp only [CollatzResearch.WordTrace]
  refine ⟨104349607365053129029401757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139132809820070838705869009 104349607365053129029401757)
  ·
    refine ⟨39131102761894923386025659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104349607365053129029401757 39131102761894923386025659)
    ·
      refine ⟨58696654142842385079038489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39131102761894923386025659 58696654142842385079038489)
      ·
        refine ⟨44022490607131788809278867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58696654142842385079038489 44022490607131788809278867)
        ·
          refine ⟨66033735910697683213918301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44022490607131788809278867 66033735910697683213918301)
          ·
            refine ⟨24762650966511631205219363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66033735910697683213918301 24762650966511631205219363)
            ·
              refine ⟨37143976449767446807829045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24762650966511631205219363 37143976449767446807829045)
              ·
                refine ⟨3482247792165698138233973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37143976449767446807829045 3482247792165698138233973)
                ·
                  refine ⟨326460730515534200459435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3482247792165698138233973 326460730515534200459435)
                  ·
                    rfl

theorem cell23_5722020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_5722020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722020 prefixEnd_5722020 := by exact prefixLift 5722020
  have htrace : WordTrace (prefixWord ++ tailWord_5722020) baseStart_5722020 baseEnd_5722020 := by
    simpa [prefixWord, tailWord_5722020, baseEnd_5722020] using wordTrace_append hprefix tailTrace_5722020
  have hstable : (prefixWord ++ tailWord_5722020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722020).length < 2 ^ (prefixWord ++ tailWord_5722020).sum := by decide
  have hdescent : baseEnd_5722020 < baseStart_5722020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722053 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_5722053 : Nat := 118140960795 + 5722053 * 2 ^ 59
def prefixEnd_5722053 : Nat := 4983230072969 + 3 ^ 40 * 5722053 * 2
def baseEnd_5722053 : Nat := 2938163519501406175022263

theorem tailTrace_5722053 : CollatzResearch.WordTrace tailWord_5722053 prefixEnd_5722053 2938163519501406175022263 := by
  unfold tailWord_5722053
  simp only [CollatzResearch.WordTrace]
  refine ⟨208700418338986704694754813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139133612225991136463169875 208700418338986704694754813)
  ·
    refine ⟨78262656877120014260533055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208700418338986704694754813 78262656877120014260533055)
    ·
      refine ⟨117393985315680021390799583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78262656877120014260533055 117393985315680021390799583)
      ·
        refine ⟨176090977973520032086199375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117393985315680021390799583 176090977973520032086199375)
        ·
          refine ⟨264136466960280048129299063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176090977973520032086199375 264136466960280048129299063)
          ·
            refine ⟨396204700440420072193948595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264136466960280048129299063 396204700440420072193948595)
            ·
              refine ⟨594307050660630108290922893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396204700440420072193948595 594307050660630108290922893)
              ·
                refine ⟨222865143997736290609096085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594307050660630108290922893 222865143997736290609096085)
                ·
                  refine ⟨10446803624893888622301379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222865143997736290609096085 10446803624893888622301379)
                  ·
                    refine ⟨15670205437340832933452069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10446803624893888622301379 15670205437340832933452069)
                    ·
                      refine ⟨2938163519501406175022263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15670205437340832933452069 2938163519501406175022263)
                      ·
                        rfl

theorem cell23_5722053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_5722053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722053 prefixEnd_5722053 := by exact prefixLift 5722053
  have htrace : WordTrace (prefixWord ++ tailWord_5722053) baseStart_5722053 baseEnd_5722053 := by
    simpa [prefixWord, tailWord_5722053, baseEnd_5722053] using wordTrace_append hprefix tailTrace_5722053
  have hstable : (prefixWord ++ tailWord_5722053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722053).length < 2 ^ (prefixWord ++ tailWord_5722053).sum := by decide
  have hdescent : baseEnd_5722053 < baseStart_5722053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722087 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_5722087 : Nat := 118140960795 + 5722087 * 2 ^ 59
def prefixEnd_5722087 : Nat := 4983230072969 + 3 ^ 40 * 5722087 * 2
def baseEnd_5722087 : Nat := 2938180977843659041997107

theorem tailTrace_5722087 : CollatzResearch.WordTrace tailWord_5722087 prefixEnd_5722087 2938180977843659041997107 := by
  unfold tailWord_5722087
  simp only [CollatzResearch.WordTrace]
  refine ⟨208701658420863528501492515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139134438947242352334328343 208701658420863528501492515)
  ·
    refine ⟨313052487631295292752238773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208701658420863528501492515 313052487631295292752238773)
    ·
      refine ⟨29348670715433933695522385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313052487631295292752238773 29348670715433933695522385)
      ·
        refine ⟨22011503036575450271641789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29348670715433933695522385 22011503036575450271641789)
        ·
          refine ⟨8254313638715793851865671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22011503036575450271641789 8254313638715793851865671)
          ·
            refine ⟨12381470458073690777798507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254313638715793851865671 12381470458073690777798507)
            ·
              refine ⟨18572205687110536166697761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12381470458073690777798507 18572205687110536166697761)
              ·
                refine ⟨13929154265332902125023321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18572205687110536166697761 13929154265332902125023321)
                ·
                  refine ⟨10446865698999676593767491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13929154265332902125023321 10446865698999676593767491)
                  ·
                    refine ⟨15670298548499514890651237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10446865698999676593767491 15670298548499514890651237)
                    ·
                      refine ⟨2938180977843659041997107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15670298548499514890651237 2938180977843659041997107)
                      ·
                        rfl

theorem cell23_5722087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_5722087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722087 prefixEnd_5722087 := by exact prefixLift 5722087
  have htrace : WordTrace (prefixWord ++ tailWord_5722087) baseStart_5722087 baseEnd_5722087 := by
    simpa [prefixWord, tailWord_5722087, baseEnd_5722087] using wordTrace_append hprefix tailTrace_5722087
  have hstable : (prefixWord ++ tailWord_5722087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722087).length < 2 ^ (prefixWord ++ tailWord_5722087).sum := by decide
  have hdescent : baseEnd_5722087 < baseStart_5722087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722118 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5722118 : Nat := 118140960795 + 5722118 * 2 ^ 59
def prefixEnd_5722118 : Nat := 4983230072969 + 3 ^ 40 * 5722118 * 2
def baseEnd_5722118 : Nat := 979398965247982806903155

theorem tailTrace_5722118 : CollatzResearch.WordTrace tailWord_5722118 prefixEnd_5722118 979398965247982806903155 := by
  unfold tailWord_5722118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521962158867225649870969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139135192722500813863914005 6521962158867225649870969)
  ·
    refine ⟨4891471619150419237403227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6521962158867225649870969 4891471619150419237403227)
    ·
      refine ⟨7337207428725628856104841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891471619150419237403227 7337207428725628856104841)
      ·
        refine ⟨5502905571544221642078631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337207428725628856104841 5502905571544221642078631)
        ·
          refine ⟨8254358357316332463117947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5502905571544221642078631 8254358357316332463117947)
          ·
            refine ⟨12381537535974498694676921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254358357316332463117947 12381537535974498694676921)
            ·
              refine ⟨9286153151980874021007691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12381537535974498694676921 9286153151980874021007691)
              ·
                refine ⟨13929229727971311031511537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9286153151980874021007691 13929229727971311031511537)
                ·
                  refine ⟨10446922295978483273633653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13929229727971311031511537 10446922295978483273633653)
                  ·
                    refine ⟨979398965247982806903155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10446922295978483273633653 979398965247982806903155)
                    ·
                      rfl

theorem cell23_5722118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5722118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722118 prefixEnd_5722118 := by exact prefixLift 5722118
  have htrace : WordTrace (prefixWord ++ tailWord_5722118) baseStart_5722118 baseEnd_5722118 := by
    simpa [prefixWord, tailWord_5722118, baseEnd_5722118] using wordTrace_append hprefix tailTrace_5722118
  have hstable : (prefixWord ++ tailWord_5722118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722118).length < 2 ^ (prefixWord ++ tailWord_5722118).sum := by decide
  have hdescent : baseEnd_5722118 < baseStart_5722118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722147 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 2, 3, 2]
def baseStart_5722147 : Nat := 118140960795 + 5722147 * 2 ^ 59
def prefixEnd_5722147 : Nat := 4983230072969 + 3 ^ 40 * 5722147 * 2
def baseEnd_5722147 : Nat := 2938211786682928807246831

theorem tailTrace_5722147 : CollatzResearch.WordTrace tailWord_5722147 prefixEnd_5722147 2938211786682928807246831 := by
  unfold tailWord_5722147
  simp only [CollatzResearch.WordTrace]
  refine ⟨208703846800646158748676695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139135897867097439165784463 208703846800646158748676695)
  ·
    refine ⟨313055770200969238123015043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208703846800646158748676695 313055770200969238123015043)
    ·
      refine ⟨469583655301453857184522565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313055770200969238123015043 469583655301453857184522565)
      ·
        refine ⟨88046935369022598222097981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469583655301453857184522565 88046935369022598222097981)
        ·
          refine ⟨33017600763383474333286743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88046935369022598222097981 33017600763383474333286743)
          ·
            refine ⟨49526401145075211499930115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33017600763383474333286743 49526401145075211499930115)
            ·
              refine ⟨74289601717612817249895173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49526401145075211499930115 74289601717612817249895173)
              ·
                refine ⟨13929300322052403234355345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74289601717612817249895173 13929300322052403234355345)
                ·
                  refine ⟨10446975241539302425766509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13929300322052403234355345 10446975241539302425766509)
                  ·
                    refine ⟨3917615715577238409662441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10446975241539302425766509 3917615715577238409662441)
                    ·
                      refine ⟨2938211786682928807246831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917615715577238409662441 2938211786682928807246831)
                      ·
                        rfl

theorem cell23_5722147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_5722147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722147 prefixEnd_5722147 := by exact prefixLift 5722147
  have htrace : WordTrace (prefixWord ++ tailWord_5722147) baseStart_5722147 baseEnd_5722147 := by
    simpa [prefixWord, tailWord_5722147, baseEnd_5722147] using wordTrace_append hprefix tailTrace_5722147
  have hstable : (prefixWord ++ tailWord_5722147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722147).length < 2 ^ (prefixWord ++ tailWord_5722147).sum := by decide
  have hdescent : baseEnd_5722147 < baseStart_5722147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722148 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_5722148 : Nat := 118140960795 + 5722148 * 2 ^ 59
def prefixEnd_5722148 : Nat := 4983230072969 + 3 ^ 40 * 5722148 * 2
def baseEnd_5722148 : Nat := 979404100054527767778109

theorem tailTrace_5722148 : CollatzResearch.WordTrace tailWord_5722148 prefixEnd_5722148 979404100054527767778109 := by
  unfold tailWord_5722148
  simp only [CollatzResearch.WordTrace]
  refine ⟨104351941636821267959731549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139135922182428357279642065 104351941636821267959731549)
  ·
    refine ⟨39131978113807975484899331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104351941636821267959731549 39131978113807975484899331)
    ·
      refine ⟨58697967170711963227348997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39131978113807975484899331 58697967170711963227348997)
      ·
        refine ⟨11005868844508493105127937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58697967170711963227348997 11005868844508493105127937)
        ·
          refine ⟨8254401633381369828845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11005868844508493105127937 8254401633381369828845953)
          ·
            refine ⟨6190801225036027371634465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8254401633381369828845953 6190801225036027371634465)
            ·
              refine ⟨4643100918777020528725849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6190801225036027371634465 4643100918777020528725849)
              ·
                refine ⟨3482325689082765396544387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643100918777020528725849 3482325689082765396544387)
                ·
                  refine ⟨5223488533624148094816581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482325689082765396544387 5223488533624148094816581)
                  ·
                    refine ⟨979404100054527767778109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223488533624148094816581 979404100054527767778109)
                    ·
                      rfl

theorem cell23_5722148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_5722148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722148 prefixEnd_5722148 := by exact prefixLift 5722148
  have htrace : WordTrace (prefixWord ++ tailWord_5722148) baseStart_5722148 baseEnd_5722148 := by
    simpa [prefixWord, tailWord_5722148, baseEnd_5722148] using wordTrace_append hprefix tailTrace_5722148
  have hstable : (prefixWord ++ tailWord_5722148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722148).length < 2 ^ (prefixWord ++ tailWord_5722148).sum := by decide
  have hdescent : baseEnd_5722148 < baseStart_5722148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722160 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_5722160 : Nat := 118140960795 + 5722160 * 2 ^ 59
def prefixEnd_5722160 : Nat := 4983230072969 + 3 ^ 40 * 5722160 * 2
def baseEnd_5722160 : Nat := 2938218461931437256384271

theorem tailTrace_5722160 : CollatzResearch.WordTrace tailWord_5722160 prefixEnd_5722160 2938218461931437256384271 := by
  unfold tailWord_5722160
  simp only [CollatzResearch.WordTrace]
  refine ⟨104352160474799530984449967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139136213966399374645933289 104352160474799530984449967)
  ·
    refine ⟨156528240712199296476674951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104352160474799530984449967 156528240712199296476674951)
    ·
      refine ⟨234792361068298944715012427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156528240712199296476674951 234792361068298944715012427)
      ·
        refine ⟨352188541602448417072518641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234792361068298944715012427 352188541602448417072518641)
        ·
          refine ⟨264141406201836312804388981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352188541602448417072518641 264141406201836312804388981)
          ·
            refine ⟨24763256831422154325411467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264141406201836312804388981 24763256831422154325411467)
            ·
              refine ⟨37144885247133231488117201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24763256831422154325411467 37144885247133231488117201)
              ·
                refine ⟨27858663935349923616087901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37144885247133231488117201 27858663935349923616087901)
                ·
                  refine ⟨10446998975756221356032963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27858663935349923616087901 10446998975756221356032963)
                  ·
                    refine ⟨15670498463634332034049445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10446998975756221356032963 15670498463634332034049445)
                    ·
                      refine ⟨2938218461931437256384271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15670498463634332034049445 2938218461931437256384271)
                      ·
                        rfl

theorem cell23_5722160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_5722160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722160 prefixEnd_5722160 := by exact prefixLift 5722160
  have htrace : WordTrace (prefixWord ++ tailWord_5722160) baseStart_5722160 baseEnd_5722160 := by
    simpa [prefixWord, tailWord_5722160, baseEnd_5722160] using wordTrace_append hprefix tailTrace_5722160
  have hstable : (prefixWord ++ tailWord_5722160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722160).length < 2 ^ (prefixWord ++ tailWord_5722160).sum := by decide
  have hdescent : baseEnd_5722160 < baseStart_5722160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722170 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_5722170 : Nat := 118140960795 + 5722170 * 2 ^ 59
def prefixEnd_5722170 : Nat := 4983230072969 + 3 ^ 40 * 5722170 * 2
def baseEnd_5722170 : Nat := 979407865579327405753075

theorem tailTrace_5722170 : CollatzResearch.WordTrace tailWord_5722170 prefixEnd_5722170 979407865579327405753075 := by
  unfold tailWord_5722170
  simp only [CollatzResearch.WordTrace]
  refine ⟨52176171419890708419190991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139136457119708555784509309 52176171419890708419190991)
  ·
    refine ⟨78264257129836062628786487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52176171419890708419190991 78264257129836062628786487)
    ·
      refine ⟨117396385694754093943179731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78264257129836062628786487 117396385694754093943179731)
      ·
        refine ⟨176094578542131140914769597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117396385694754093943179731 176094578542131140914769597)
        ·
          refine ⟨66035466953299177843038599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176094578542131140914769597 66035466953299177843038599)
          ·
            refine ⟨99053200429948766764557899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66035466953299177843038599 99053200429948766764557899)
            ·
              refine ⟨148579800644923150146836849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99053200429948766764557899 148579800644923150146836849)
              ·
                refine ⟨111434850483692362610127637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148579800644923150146836849 111434850483692362610127637)
                ·
                  refine ⟨5223508616423079497349733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111434850483692362610127637 5223508616423079497349733)
                  ·
                    refine ⟨979407865579327405753075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223508616423079497349733 979407865579327405753075)
                    ·
                      rfl

theorem cell23_5722170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_5722170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722170 prefixEnd_5722170 := by exact prefixLift 5722170
  have htrace : WordTrace (prefixWord ++ tailWord_5722170) baseStart_5722170 baseEnd_5722170 := by
    simpa [prefixWord, tailWord_5722170, baseEnd_5722170] using wordTrace_append hprefix tailTrace_5722170
  have hstable : (prefixWord ++ tailWord_5722170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722170).length < 2 ^ (prefixWord ++ tailWord_5722170).sum := by decide
  have hdescent : baseEnd_5722170 < baseStart_5722170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722177 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5722177 : Nat := 118140960795 + 5722177 * 2 ^ 59
def prefixEnd_5722177 : Nat := 4983230072969 + 3 ^ 40 * 5722177 * 2
def baseEnd_5722177 : Nat := 2938227191102563689871693

theorem tailTrace_5722177 : CollatzResearch.WordTrace tailWord_5722177 prefixEnd_5722177 2938227191102563689871693 := by
  unfold tailWord_5722177
  simp only [CollatzResearch.WordTrace]
  refine ⟨208704940990537473872268785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139136627327024982581512523 208704940990537473872268785)
  ·
    refine ⟨156528705742903105404201589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208704940990537473872268785 156528705742903105404201589)
    ·
      refine ⟨14674566163397166131643899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156528705742903105404201589 14674566163397166131643899)
      ·
        refine ⟨22011849245095749197465849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14674566163397166131643899 22011849245095749197465849)
        ·
          refine ⟨16508886933821811898099387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22011849245095749197465849 16508886933821811898099387)
          ·
            refine ⟨24763330400732717847149081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16508886933821811898099387 24763330400732717847149081)
            ·
              refine ⟨18572497800549538385361811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24763330400732717847149081 18572497800549538385361811)
              ·
                refine ⟨27858746700824307578042717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18572497800549538385361811 27858746700824307578042717)
                ·
                  refine ⟨10447030012809115341766019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27858746700824307578042717 10447030012809115341766019)
                  ·
                    refine ⟨15670545019213673012649029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10447030012809115341766019 15670545019213673012649029)
                    ·
                      refine ⟨2938227191102563689871693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15670545019213673012649029 2938227191102563689871693)
                      ·
                        rfl

theorem cell23_5722177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5722177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722177 prefixEnd_5722177 := by exact prefixLift 5722177
  have htrace : WordTrace (prefixWord ++ tailWord_5722177) baseStart_5722177 baseEnd_5722177 := by
    simpa [prefixWord, tailWord_5722177, baseEnd_5722177] using wordTrace_append hprefix tailTrace_5722177
  have hstable : (prefixWord ++ tailWord_5722177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722177).length < 2 ^ (prefixWord ++ tailWord_5722177).sum := by decide
  have hdescent : baseEnd_5722177 < baseStart_5722177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722194 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_5722194 : Nat := 118140960795 + 5722194 * 2 ^ 59
def prefixEnd_5722194 : Nat := 4983230072969 + 3 ^ 40 * 5722194 * 2
def baseEnd_5722194 : Nat := 2938235920273690123359115

theorem tailTrace_5722194 : CollatzResearch.WordTrace tailWord_5722194 prefixEnd_5722194 2938235920273690123359115 := by
  unfold tailWord_5722194
  simp only [CollatzResearch.WordTrace]
  refine ⟨52176390257868971443909409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139137040687650590517091757 52176390257868971443909409)
  ·
    refine ⟨39132292693401728582932057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52176390257868971443909409 39132292693401728582932057)
    ·
      refine ⟨29349219520051296437199043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39132292693401728582932057 29349219520051296437199043)
      ·
        refine ⟨44023829280076944655798565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29349219520051296437199043 44023829280076944655798565)
        ·
          refine ⟨8254467990014427122962231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44023829280076944655798565 8254467990014427122962231)
          ·
            refine ⟨12381701985021640684443347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254467990014427122962231 12381701985021640684443347)
            ·
              refine ⟨18572552977532461026665021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12381701985021640684443347 18572552977532461026665021)
              ·
                refine ⟨6964707366574672884999383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18572552977532461026665021 6964707366574672884999383)
                ·
                  refine ⟨10447061049862009327499075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6964707366574672884999383 10447061049862009327499075)
                  ·
                    refine ⟨15670591574793013991248613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10447061049862009327499075 15670591574793013991248613)
                    ·
                      refine ⟨2938235920273690123359115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15670591574793013991248613 2938235920273690123359115)
                      ·
                        rfl

theorem cell23_5722194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_5722194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722194 prefixEnd_5722194 := by exact prefixLift 5722194
  have htrace : WordTrace (prefixWord ++ tailWord_5722194) baseStart_5722194 baseEnd_5722194 := by
    simpa [prefixWord, tailWord_5722194, baseEnd_5722194] using wordTrace_append hprefix tailTrace_5722194
  have hstable : (prefixWord ++ tailWord_5722194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722194).length < 2 ^ (prefixWord ++ tailWord_5722194).sum := by decide
  have hdescent : baseEnd_5722194 < baseStart_5722194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722204 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_5722204 : Nat := 118140960795 + 5722204 * 2 ^ 59
def prefixEnd_5722204 : Nat := 4983230072969 + 3 ^ 40 * 5722204 * 2
def baseEnd_5722204 : Nat := 979413685026745028078023

theorem tailTrace_5722204 : CollatzResearch.WordTrace tailWord_5722204 prefixEnd_5722204 979413685026745028078023 := by
  unfold tailWord_5722204
  simp only [CollatzResearch.WordTrace]
  refine ⟨104352962880719828741750833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139137283840959771655667777 104352962880719828741750833)
  ·
    refine ⟨78264722160539871556313125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104352962880719828741750833 78264722160539871556313125)
    ·
      refine ⟨14674635405101225916808711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78264722160539871556313125 14674635405101225916808711)
      ·
        refine ⟨22011953107651838875213067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14674635405101225916808711 22011953107651838875213067)
        ·
          refine ⟨33017929661477758312819601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22011953107651838875213067 33017929661477758312819601)
          ·
            refine ⟨24763447246108318734614701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33017929661477758312819601 24763447246108318734614701)
            ·
              refine ⟨9286292717290619525480513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24763447246108318734614701 9286292717290619525480513)
              ·
                refine ⟨6964719537967964644110385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9286292717290619525480513 6964719537967964644110385)
                ·
                  refine ⟨5223539653475973483082789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6964719537967964644110385 5223539653475973483082789)
                  ·
                    refine ⟨979413685026745028078023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223539653475973483082789 979413685026745028078023)
                    ·
                      rfl

theorem cell23_5722204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_5722204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722204 prefixEnd_5722204 := by exact prefixLift 5722204
  have htrace : WordTrace (prefixWord ++ tailWord_5722204) baseStart_5722204 baseEnd_5722204 := by
    simpa [prefixWord, tailWord_5722204, baseEnd_5722204] using wordTrace_append hprefix tailTrace_5722204
  have hstable : (prefixWord ++ tailWord_5722204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722204).length < 2 ^ (prefixWord ++ tailWord_5722204).sum := by decide
  have hdescent : baseEnd_5722204 < baseStart_5722204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722211 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 1, 2, 2]
def baseStart_5722211 : Nat := 118140960795 + 5722211 * 2 ^ 59
def prefixEnd_5722211 : Nat := 4983230072969 + 3 ^ 40 * 5722211 * 2
def baseEnd_5722211 : Nat := 2938244649444816556846537

theorem tailTrace_5722211 : CollatzResearch.WordTrace tailWord_5722211 prefixEnd_5722211 2938244649444816556846537 := by
  unfold tailWord_5722211
  simp only [CollatzResearch.WordTrace]
  refine ⟨208706181072414297679006487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139137454048276198452670991 208706181072414297679006487)
  ·
    refine ⟨313059271608621446518509731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208706181072414297679006487 313059271608621446518509731)
    ·
      refine ⟨469588907412932169777764597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313059271608621446518509731 469588907412932169777764597)
      ·
        refine ⟨44023960069962390916665431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 469588907412932169777764597 44023960069962390916665431)
        ·
          refine ⟨66035940104943586374998147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44023960069962390916665431 66035940104943586374998147)
          ·
            refine ⟨99053910157415379562497221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66035940104943586374998147 99053910157415379562497221)
            ·
              refine ⟨18572608154515383667968229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99053910157415379562497221 18572608154515383667968229)
              ·
                refine ⟨3482364028971634437744043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18572608154515383667968229 3482364028971634437744043)
                ·
                  refine ⟨5223546043457451656616065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482364028971634437744043 5223546043457451656616065)
                  ·
                    refine ⟨3917659532593088742462049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5223546043457451656616065 3917659532593088742462049)
                    ·
                      refine ⟨2938244649444816556846537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917659532593088742462049 2938244649444816556846537)
                      ·
                        rfl

theorem cell23_5722211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_5722211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722211 prefixEnd_5722211 := by exact prefixLift 5722211
  have htrace : WordTrace (prefixWord ++ tailWord_5722211) baseStart_5722211 baseEnd_5722211 := by
    simpa [prefixWord, tailWord_5722211, baseEnd_5722211] using wordTrace_append hprefix tailTrace_5722211
  have hstable : (prefixWord ++ tailWord_5722211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722211).length < 2 ^ (prefixWord ++ tailWord_5722211).sum := by decide
  have hdescent : baseEnd_5722211 < baseStart_5722211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722290 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_5722290 : Nat := 118140960795 + 5722290 * 2 ^ 59
def prefixEnd_5722290 : Nat := 4983230072969 + 3 ^ 40 * 5722290 * 2
def baseEnd_5722290 : Nat := 326476134935169083084297

theorem tailTrace_5722290 : CollatzResearch.WordTrace tailWord_5722290 prefixEnd_5722290 326476134935169083084297 := by
  unfold tailWord_5722290
  simp only [CollatzResearch.WordTrace]
  refine ⟨52177265609782023542783081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139139374959418729447421549 52177265609782023542783081)
  ·
    refine ⟨39132949207336517657087311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52177265609782023542783081 39132949207336517657087311)
    ·
      refine ⟨58699423811004776485630967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39132949207336517657087311 58699423811004776485630967)
      ·
        refine ⟨88049135716507164728446451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58699423811004776485630967 88049135716507164728446451)
        ·
          refine ⟨132073703574760747092669677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88049135716507164728446451 132073703574760747092669677)
          ·
            refine ⟨49527638840535280159751129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132073703574760747092669677 49527638840535280159751129)
            ·
              refine ⟨37145729130401460119813347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49527638840535280159751129 37145729130401460119813347)
              ·
                refine ⟨55718593695602190179720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37145729130401460119813347 55718593695602190179720021)
                ·
                  refine ⟨326476134935169083084297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55718593695602190179720021 326476134935169083084297)
                  ·
                    rfl

theorem cell23_5722290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_5722290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722290 prefixEnd_5722290 := by exact prefixLift 5722290
  have htrace : WordTrace (prefixWord ++ tailWord_5722290) baseStart_5722290 baseEnd_5722290 := by
    simpa [prefixWord, tailWord_5722290, baseEnd_5722290] using wordTrace_append hprefix tailTrace_5722290
  have hstable : (prefixWord ++ tailWord_5722290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722290).length < 2 ^ (prefixWord ++ tailWord_5722290).sum := by decide
  have hdescent : baseEnd_5722290 < baseStart_5722290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722305 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5722305 : Nat := 118140960795 + 5722305 * 2 ^ 59
def prefixEnd_5722305 : Nat := 4983230072969 + 3 ^ 40 * 5722305 * 2
def baseEnd_5722305 : Nat := 2938292916626339189071105

theorem tailTrace_5722305 : CollatzResearch.WordTrace tailWord_5722305 prefixEnd_5722305 2938292916626339189071105 := by
  unfold tailWord_5722305
  simp only [CollatzResearch.WordTrace]
  refine ⟨208709609534073751732928369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139139739689382501155285579 208709609534073751732928369)
  ·
    refine ⟨156532207150555313799696277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208709609534073751732928369 156532207150555313799696277)
    ·
      refine ⟨7337447210182280334360763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156532207150555313799696277 7337447210182280334360763)
      ·
        refine ⟨11006170815273420501541145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337447210182280334360763 11006170815273420501541145)
        ·
          refine ⟨8254628111455065376155859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006170815273420501541145 8254628111455065376155859)
          ·
            refine ⟨12381942167182598064233789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254628111455065376155859 12381942167182598064233789)
            ·
              refine ⟨4643228312693474274087671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12381942167182598064233789 4643228312693474274087671)
              ·
                refine ⟨6964842469040211411131507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4643228312693474274087671 6964842469040211411131507)
                ·
                  refine ⟨10447263703560317116697261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6964842469040211411131507 10447263703560317116697261)
                  ·
                    refine ⟨3917723888835118918761473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10447263703560317116697261 3917723888835118918761473)
                    ·
                      refine ⟨2938292916626339189071105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917723888835118918761473 2938292916626339189071105)
                      ·
                        rfl

theorem cell23_5722305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5722305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722305 prefixEnd_5722305 := by exact prefixLift 5722305
  have htrace : WordTrace (prefixWord ++ tailWord_5722305) baseStart_5722305 baseEnd_5722305 := by
    simpa [prefixWord, tailWord_5722305, baseEnd_5722305] using wordTrace_append hprefix tailTrace_5722305
  have hstable : (prefixWord ++ tailWord_5722305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722305).length < 2 ^ (prefixWord ++ tailWord_5722305).sum := by decide
  have hdescent : baseEnd_5722305 < baseStart_5722305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722318 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_5722318 : Nat := 118140960795 + 5722318 * 2 ^ 59
def prefixEnd_5722318 : Nat := 4983230072969 + 3 ^ 40 * 5722318 * 2
def baseEnd_5722318 : Nat := 2938299591874847638208545

theorem tailTrace_5722318 : CollatzResearch.WordTrace tailWord_5722318 prefixEnd_5722318 2938299591874847638208545 := by
  unfold tailWord_5722318
  simp only [CollatzResearch.WordTrace]
  refine ⟨26088760460378331869143951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139140055788684436635434405 26088760460378331869143951)
  ·
    refine ⟨39133140690567497803715927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26088760460378331869143951 39133140690567497803715927)
    ·
      refine ⟨58699711035851246705573891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39133140690567497803715927 58699711035851246705573891)
      ·
        refine ⟨88049566553776870058360837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58699711035851246705573891 88049566553776870058360837)
        ·
          refine ⟨16509293728833163135942657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88049566553776870058360837 16509293728833163135942657)
          ·
            refine ⟨12381970296624872351956993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16509293728833163135942657 12381970296624872351956993)
            ·
              refine ⟨9286477722468654263967745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12381970296624872351956993 9286477722468654263967745)
              ·
                refine ⟨6964858291851490697975809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9286477722468654263967745 6964858291851490697975809)
                ·
                  refine ⟨5223643718888618023481857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6964858291851490697975809 5223643718888618023481857)
                  ·
                    refine ⟨3917732789166463517611393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5223643718888618023481857 3917732789166463517611393)
                    ·
                      refine ⟨2938299591874847638208545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917732789166463517611393 2938299591874847638208545)
                      ·
                        rfl

theorem cell23_5722318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_5722318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722318 prefixEnd_5722318 := by exact prefixLift 5722318
  have htrace : WordTrace (prefixWord ++ tailWord_5722318) baseStart_5722318 baseEnd_5722318 := by
    simpa [prefixWord, tailWord_5722318, baseEnd_5722318] using wordTrace_append hprefix tailTrace_5722318
  have hstable : (prefixWord ++ tailWord_5722318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722318).length < 2 ^ (prefixWord ++ tailWord_5722318).sum := by decide
  have hdescent : baseEnd_5722318 < baseStart_5722318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722354 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_5722354 : Nat := 118140960795 + 5722354 * 2 ^ 59
def prefixEnd_5722354 : Nat := 4983230072969 + 3 ^ 40 * 5722354 * 2
def baseEnd_5722354 : Nat := 979439359059469832452793

theorem tailTrace_5722354 : CollatzResearch.WordTrace tailWord_5722354 prefixEnd_5722354 979439359059469832452793 := by
  unfold tailWord_5722354
  simp only [CollatzResearch.WordTrace]
  refine ⟨52177849177724058275365529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139140931140597488734308077 52177849177724058275365529)
  ·
    refine ⟨39133386883293043706524147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52177849177724058275365529 39133386883293043706524147)
    ·
      refine ⟨58700080324939565559786221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39133386883293043706524147 58700080324939565559786221)
      ·
        refine ⟨22012530121852337084919833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58700080324939565559786221 22012530121852337084919833)
        ·
          refine ⟨16509397591389252813689875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22012530121852337084919833 16509397591389252813689875)
          ·
            refine ⟨24764096387083879220534813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16509397591389252813689875 24764096387083879220534813)
            ·
              refine ⟨9286536145156454707700555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24764096387083879220534813 9286536145156454707700555)
              ·
                refine ⟨13929804217734682061550833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9286536145156454707700555 13929804217734682061550833)
                ·
                  refine ⟨10447353163301011546163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13929804217734682061550833 10447353163301011546163125)
                  ·
                    refine ⟨979439359059469832452793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10447353163301011546163125 979439359059469832452793)
                    ·
                      rfl

theorem cell23_5722354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_5722354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722354 prefixEnd_5722354 := by exact prefixLift 5722354
  have htrace : WordTrace (prefixWord ++ tailWord_5722354) baseStart_5722354 baseEnd_5722354 := by
    simpa [prefixWord, tailWord_5722354, baseEnd_5722354] using wordTrace_append hprefix tailTrace_5722354
  have hstable : (prefixWord ++ tailWord_5722354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722354).length < 2 ^ (prefixWord ++ tailWord_5722354).sum := by decide
  have hdescent : baseEnd_5722354 < baseStart_5722354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722367 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 5, 4]
def baseStart_5722367 : Nat := 118140960795 + 5722367 * 2 ^ 59
def prefixEnd_5722367 : Nat := 4983230072969 + 3 ^ 40 * 5722367 * 2
def baseEnd_5722367 : Nat := 979441584142305982165273

theorem tailTrace_5722367 : CollatzResearch.WordTrace tailWord_5722367 prefixEnd_5722367 979441584142305982165273 := by
  unfold tailWord_5722367
  simp only [CollatzResearch.WordTrace]
  refine ⟨208711870859849136321685355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139141247239899424214456903 208711870859849136321685355)
  ·
    refine ⟨313067806289773704482528033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208711870859849136321685355 313067806289773704482528033)
    ·
      refine ⟨234800854717330278361896025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313067806289773704482528033 234800854717330278361896025)
      ·
        refine ⟨176100641037997708771422019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234800854717330278361896025 176100641037997708771422019)
        ·
          refine ⟨264150961556996563157133029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176100641037997708771422019 264150961556996563157133029)
          ·
            refine ⟨49528305291936855591962443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264150961556996563157133029 49528305291936855591962443)
            ·
              refine ⟨74292457937905283387943665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49528305291936855591962443 74292457937905283387943665)
              ·
                refine ⟨55719343453428962540957749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74292457937905283387943665 55719343453428962540957749)
                ·
                  refine ⟨5223688448758965238214789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55719343453428962540957749 5223688448758965238214789)
                  ·
                    refine ⟨979441584142305982165273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223688448758965238214789 979441584142305982165273)
                    ·
                      rfl

theorem cell23_5722367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_5722367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722367 prefixEnd_5722367 := by exact prefixLift 5722367
  have htrace : WordTrace (prefixWord ++ tailWord_5722367) baseStart_5722367 baseEnd_5722367 := by
    simpa [prefixWord, tailWord_5722367, baseEnd_5722367] using wordTrace_append hprefix tailTrace_5722367
  have hstable : (prefixWord ++ tailWord_5722367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722367).length < 2 ^ (prefixWord ++ tailWord_5722367).sum := by decide
  have hdescent : baseEnd_5722367 < baseStart_5722367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722424 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_5722424 : Nat := 118140960795 + 5722424 * 2 ^ 59
def prefixEnd_5722424 : Nat := 4983230072969 + 3 ^ 40 * 5722424 * 2
def baseEnd_5722424 : Nat := 2938354020824224223483057

theorem tailTrace_5722424 : CollatzResearch.WordTrace tailWord_5722424 prefixEnd_5722424 2938354020824224223483057 := by
  unfold tailWord_5722424
  simp only [CollatzResearch.WordTrace]
  refine ⟨104356974910321317528255163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139142633213761756704340217 104356974910321317528255163)
  ·
    refine ⟨156535462365481976292382745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104356974910321317528255163 156535462365481976292382745)
    ·
      refine ⟨117401596774111482219287059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156535462365481976292382745 117401596774111482219287059)
      ·
        refine ⟨176102395161167223328930589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117401596774111482219287059 176102395161167223328930589)
        ·
          refine ⟨66038398185437708748348971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176102395161167223328930589 66038398185437708748348971)
          ·
            refine ⟨99057597278156563122523457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66038398185437708748348971 99057597278156563122523457)
            ·
              refine ⟨74293197958617422341892593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99057597278156563122523457 74293197958617422341892593)
              ·
                refine ⟨55719898468963066756419445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74293197958617422341892593 55719898468963066756419445)
                ·
                  refine ⟨5223740481465287508414323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55719898468963066756419445 5223740481465287508414323)
                  ·
                    refine ⟨7835610722197931262621485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5223740481465287508414323 7835610722197931262621485)
                    ·
                      refine ⟨2938354020824224223483057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7835610722197931262621485 2938354020824224223483057)
                      ·
                        rfl

theorem cell23_5722424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_5722424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722424 prefixEnd_5722424 := by exact prefixLift 5722424
  have htrace : WordTrace (prefixWord ++ tailWord_5722424) baseStart_5722424 baseEnd_5722424 := by
    simpa [prefixWord, tailWord_5722424, baseEnd_5722424] using wordTrace_append hprefix tailTrace_5722424
  have hstable : (prefixWord ++ tailWord_5722424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722424).length < 2 ^ (prefixWord ++ tailWord_5722424).sum := by decide
  have hdescent : baseEnd_5722424 < baseStart_5722424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722457 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_5722457 : Nat := 118140960795 + 5722457 * 2 ^ 59
def prefixEnd_5722457 : Nat := 4983230072969 + 3 ^ 40 * 5722457 * 2
def baseEnd_5722457 : Nat := 979456988561940864790135

theorem tailTrace_5722457 : CollatzResearch.WordTrace tailWord_5722457 prefixEnd_5722457 979456988561940864790135 := by
  unfold tailWord_5722457
  simp only [CollatzResearch.WordTrace]
  refine ⟨208715153429523081692461625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139143435619682054461641083 208715153429523081692461625)
  ·
    refine ⟨156536365072142311269346219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208715153429523081692461625 156536365072142311269346219)
    ·
      refine ⟨234804547608213466904019329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156536365072142311269346219 234804547608213466904019329)
      ·
        refine ⟨176103410706160100178014497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234804547608213466904019329 176103410706160100178014497)
        ·
          refine ⟨132077558029620075133510873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176103410706160100178014497 132077558029620075133510873)
          ·
            refine ⟨99058168522215056350133155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132077558029620075133510873 99058168522215056350133155)
            ·
              refine ⟨148587252783322584525199733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99058168522215056350133155 148587252783322584525199733)
              ·
                refine ⟨13930054948436492299237475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148587252783322584525199733 13930054948436492299237475)
                ·
                  refine ⟨20895082422654738448856213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13930054948436492299237475 20895082422654738448856213)
                  ·
                    refine ⟨979456988561940864790135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20895082422654738448856213 979456988561940864790135)
                    ·
                      rfl

theorem cell23_5722457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_5722457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722457 prefixEnd_5722457 := by exact prefixLift 5722457
  have htrace : WordTrace (prefixWord ++ tailWord_5722457) baseStart_5722457 baseEnd_5722457 := by
    simpa [prefixWord, tailWord_5722457, baseEnd_5722457] using wordTrace_append hprefix tailTrace_5722457
  have hstable : (prefixWord ++ tailWord_5722457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722457).length < 2 ^ (prefixWord ++ tailWord_5722457).sum := by decide
  have hdescent : baseEnd_5722457 < baseStart_5722457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722474 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_5722474 : Nat := 118140960795 + 5722474 * 2 ^ 59
def prefixEnd_5722474 : Nat := 4983230072969 + 3 ^ 40 * 5722474 * 2
def baseEnd_5722474 : Nat := 979459898285649675952609

theorem tailTrace_5722474 : CollatzResearch.WordTrace tailWord_5722474 prefixEnd_5722474 979459898285649675952609 := by
  unfold tailWord_5722474
  simp only [CollatzResearch.WordTrace]
  refine ⟨52178943367615373398957619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139143848980307662397220317 52178943367615373398957619)
  ·
    refine ⟨78268415051423060098436429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52178943367615373398957619 78268415051423060098436429)
    ·
      refine ⟨29350655644283647536913661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78268415051423060098436429 29350655644283647536913661)
      ·
        refine ⟨11006495866606367826342623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29350655644283647536913661 11006495866606367826342623)
        ·
          refine ⟨16509743799909551739513935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11006495866606367826342623 16509743799909551739513935)
          ·
            refine ⟨24764615699864327609270903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16509743799909551739513935 24764615699864327609270903)
            ·
              refine ⟨37146923549796491413906355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24764615699864327609270903 37146923549796491413906355)
              ·
                refine ⟨55720385324694737120859533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37146923549796491413906355 55720385324694737120859533)
                ·
                  refine ⟨20895144496760526420322325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55720385324694737120859533 20895144496760526420322325)
                  ·
                    refine ⟨979459898285649675952609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20895144496760526420322325 979459898285649675952609)
                    ·
                      rfl

theorem cell23_5722474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_5722474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722474 prefixEnd_5722474 := by exact prefixLift 5722474
  have htrace : WordTrace (prefixWord ++ tailWord_5722474) baseStart_5722474 baseEnd_5722474 := by
    simpa [prefixWord, tailWord_5722474, baseEnd_5722474] using wordTrace_append hprefix tailTrace_5722474
  have hstable : (prefixWord ++ tailWord_5722474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722474).length < 2 ^ (prefixWord ++ tailWord_5722474).sum := by decide
  have hdescent : baseEnd_5722474 < baseStart_5722474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722491 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 2, 4]
def baseStart_5722491 : Nat := 118140960795 + 5722491 * 2 ^ 59
def prefixEnd_5722491 : Nat := 4983230072969 + 3 ^ 40 * 5722491 * 2
def baseEnd_5722491 : Nat := 979462808009358487115083

theorem tailTrace_5722491 : CollatzResearch.WordTrace tailWord_5722491 prefixEnd_5722491 979462808009358487115083 := by
  unfold tailWord_5722491
  simp only [CollatzResearch.WordTrace]
  refine ⟨208716393511399905499199327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139144262340933270332799551 208716393511399905499199327)
  ·
    refine ⟨313074590267099858248798991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208716393511399905499199327 313074590267099858248798991)
    ·
      refine ⟨469611885400649787373198487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313074590267099858248798991 469611885400649787373198487)
      ·
        refine ⟨704417828100974681059797731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469611885400649787373198487 704417828100974681059797731)
        ·
          refine ⟨1056626742151462021589696597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704417828100974681059797731 1056626742151462021589696597)
          ·
            refine ⟨12382344634587445565504257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1056626742151462021589696597 12382344634587445565504257)
            ·
              refine ⟨9286758475940584174128193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382344634587445565504257 9286758475940584174128193)
              ·
                refine ⟨6965068856955438130596145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9286758475940584174128193 6965068856955438130596145)
                ·
                  refine ⟨5223801642716578597947109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6965068856955438130596145 5223801642716578597947109)
                  ·
                    refine ⟨979462808009358487115083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223801642716578597947109 979462808009358487115083)
                    ·
                      rfl

theorem cell23_5722491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 4].length) (baseStart_5722491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722491 prefixEnd_5722491 := by exact prefixLift 5722491
  have htrace : WordTrace (prefixWord ++ tailWord_5722491) baseStart_5722491 baseEnd_5722491 := by
    simpa [prefixWord, tailWord_5722491, baseEnd_5722491] using wordTrace_append hprefix tailTrace_5722491
  have hstable : (prefixWord ++ tailWord_5722491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722491).length < 2 ^ (prefixWord ++ tailWord_5722491).sum := by decide
  have hdescent : baseEnd_5722491 < baseStart_5722491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722517 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_5722517 : Nat := 118140960795 + 5722517 * 2 ^ 59
def prefixEnd_5722517 : Nat := 4983230072969 + 3 ^ 40 * 5722517 * 2
def baseEnd_5722517 : Nat := 979467258175030786540043

theorem tailTrace_5722517 : CollatzResearch.WordTrace tailWord_5722517 prefixEnd_5722517 979467258175030786540043 := by
  unfold tailWord_5722517
  simp only [CollatzResearch.WordTrace]
  refine ⟨208717341809305711939645805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139144894539537141293097203 208717341809305711939645805)
  ·
    refine ⟨78269003178489641977367177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208717341809305711939645805 78269003178489641977367177)
    ·
      refine ⟨58701752383867231483025383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78269003178489641977367177 58701752383867231483025383)
      ·
        refine ⟨88052628575800847224538075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58701752383867231483025383 88052628575800847224538075)
        ·
          refine ⟨132078942863701270836807113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88052628575800847224538075 132078942863701270836807113)
          ·
            refine ⟨99059207147775953127605335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132078942863701270836807113 99059207147775953127605335)
            ·
              refine ⟨148588810721663929691408003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99059207147775953127605335 148588810721663929691408003)
              ·
                refine ⟨222883216082495894537112005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148588810721663929691408003 222883216082495894537112005)
                ·
                  refine ⟨41790603015467980225708501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222883216082495894537112005 41790603015467980225708501)
                  ·
                    refine ⟨979467258175030786540043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41790603015467980225708501 979467258175030786540043)
                    ·
                      rfl

theorem cell23_5722517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_5722517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722517 prefixEnd_5722517 := by exact prefixLift 5722517
  have htrace : WordTrace (prefixWord ++ tailWord_5722517) baseStart_5722517 baseEnd_5722517 := by
    simpa [prefixWord, tailWord_5722517, baseEnd_5722517] using wordTrace_append hprefix tailTrace_5722517
  have hstable : (prefixWord ++ tailWord_5722517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722517).length < 2 ^ (prefixWord ++ tailWord_5722517).sum := by decide
  have hdescent : baseEnd_5722517 < baseStart_5722517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722535 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5722535 : Nat := 118140960795 + 5722535 * 2 ^ 59
def prefixEnd_5722535 : Nat := 4983230072969 + 3 ^ 40 * 5722535 * 2
def baseEnd_5722535 : Nat := 2938411017176873289195047

theorem tailTrace_5722535 : CollatzResearch.WordTrace tailWord_5722535 prefixEnd_5722535 2938411017176873289195047 := by
  unfold tailWord_5722535
  simp only [CollatzResearch.WordTrace]
  refine ⟨208717998323240501013801059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139145332215493667342534039 208717998323240501013801059)
  ·
    refine ⟨313076997484860751520701589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208717998323240501013801059 313076997484860751520701589)
    ·
      refine ⟨14675484257102847727532887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 313076997484860751520701589 14675484257102847727532887)
      ·
        refine ⟨22013226385654271591299331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14675484257102847727532887 22013226385654271591299331)
        ·
          refine ⟨33019839578481407386948997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22013226385654271591299331 33019839578481407386948997)
          ·
            refine ⟨6191219920965263885052937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33019839578481407386948997 6191219920965263885052937)
            ·
              refine ⟨4643414940723947913789703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6191219920965263885052937 4643414940723947913789703)
              ·
                refine ⟨6965122411085921870684555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4643414940723947913789703 6965122411085921870684555)
                ·
                  refine ⟨10447683616628882806026833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6965122411085921870684555 10447683616628882806026833)
                  ·
                    refine ⟨7835762712471662104520125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10447683616628882806026833 7835762712471662104520125)
                    ·
                      refine ⟨2938411017176873289195047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7835762712471662104520125 2938411017176873289195047)
                      ·
                        rfl

theorem cell23_5722535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5722535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722535 prefixEnd_5722535 := by exact prefixLift 5722535
  have htrace : WordTrace (prefixWord ++ tailWord_5722535) baseStart_5722535 baseEnd_5722535 := by
    simpa [prefixWord, tailWord_5722535, baseEnd_5722535] using wordTrace_append hprefix tailTrace_5722535
  have hstable : (prefixWord ++ tailWord_5722535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722535).length < 2 ^ (prefixWord ++ tailWord_5722535).sum := by decide
  have hdescent : baseEnd_5722535 < baseStart_5722535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722538 : List Nat := [3, 1, 6, 1, 1, 1, 10]
def baseStart_5722538 : Nat := 118140960795 + 5722538 * 2 ^ 59
def prefixEnd_5722538 : Nat := 4983230072969 + 3 ^ 40 * 5722538 * 2
def baseEnd_5722538 : Nat := 36276698242207861450093

theorem tailTrace_5722538 : CollatzResearch.WordTrace tailWord_5722538 prefixEnd_5722538 36276698242207861450093 := by
  unfold tailWord_5722538
  simp only [CollatzResearch.WordTrace]
  refine ⟨52179526935557408131540067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139145405161486421684106845 52179526935557408131540067)
  ·
    refine ⟨78269290403336112197310101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52179526935557408131540067 78269290403336112197310101)
    ·
      refine ⟨3668872987656380259248911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78269290403336112197310101 3668872987656380259248911)
      ·
        refine ⟨5503309481484570388873367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3668872987656380259248911 5503309481484570388873367)
        ·
          refine ⟨8254964222226855583310051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503309481484570388873367 8254964222226855583310051)
          ·
            refine ⟨12382446333340283374965077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254964222226855583310051 12382446333340283374965077)
            ·
              refine ⟨36276698242207861450093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12382446333340283374965077 36276698242207861450093)
              ·
                rfl

theorem cell23_5722538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 10].length) (baseStart_5722538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722538 prefixEnd_5722538 := by exact prefixLift 5722538
  have htrace : WordTrace (prefixWord ++ tailWord_5722538) baseStart_5722538 baseEnd_5722538 := by
    simpa [prefixWord, tailWord_5722538, baseEnd_5722538] using wordTrace_append hprefix tailTrace_5722538
  have hstable : (prefixWord ++ tailWord_5722538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722538).length < 2 ^ (prefixWord ++ tailWord_5722538).sum := by decide
  have hdescent : baseEnd_5722538 < baseStart_5722538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722574 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_5722574 : Nat := 118140960795 + 5722574 * 2 ^ 59
def prefixEnd_5722574 : Nat := 4983230072969 + 3 ^ 40 * 5722574 * 2
def baseEnd_5722574 : Nat := 2938431042922398636607367

theorem tailTrace_5722574 : CollatzResearch.WordTrace tailWord_5722574 prefixEnd_5722574 2938431042922398636607367 := by
  unfold tailWord_5722574
  simp only [CollatzResearch.WordTrace]
  refine ⟨26089927596262401334308847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139146280513399473782980517 26089927596262401334308847)
  ·
    refine ⟨39134891394393602001463271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26089927596262401334308847 39134891394393602001463271)
    ·
      refine ⟨58702337091590403002194907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39134891394393602001463271 58702337091590403002194907)
      ·
        refine ⟨88053505637385604503292361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58702337091590403002194907 88053505637385604503292361)
        ·
          refine ⟨66040129228039203377469271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88053505637385604503292361 66040129228039203377469271)
          ·
            refine ⟨99060193842058805066203907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66040129228039203377469271 99060193842058805066203907)
            ·
              refine ⟨148590290763088207599305861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99060193842058805066203907 148590290763088207599305861)
              ·
                refine ⟨27860679518079038924869849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148590290763088207599305861 27860679518079038924869849)
                ·
                  refine ⟨20895509638559279193652387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27860679518079038924869849 20895509638559279193652387)
                  ·
                    refine ⟨31343264457838918790478581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20895509638559279193652387 31343264457838918790478581)
                    ·
                      refine ⟨2938431042922398636607367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31343264457838918790478581 2938431042922398636607367)
                      ·
                        rfl

theorem cell23_5722574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_5722574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722574 prefixEnd_5722574 := by exact prefixLift 5722574
  have htrace : WordTrace (prefixWord ++ tailWord_5722574) baseStart_5722574 baseEnd_5722574 := by
    simpa [prefixWord, tailWord_5722574, baseEnd_5722574] using wordTrace_append hprefix tailTrace_5722574
  have hstable : (prefixWord ++ tailWord_5722574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722574).length < 2 ^ (prefixWord ++ tailWord_5722574).sum := by decide
  have hdescent : baseEnd_5722574 < baseStart_5722574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722605 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5722605 : Nat := 118140960795 + 5722605 * 2 ^ 59
def prefixEnd_5722605 : Nat := 4983230072969 + 3 ^ 40 * 5722605 * 2
def baseEnd_5722605 : Nat := 2938446960822688015319725

theorem tailTrace_5722605 : CollatzResearch.WordTrace tailWord_5722605 prefixEnd_5722605 2938446960822688015319725 := by
  unfold tailWord_5722605
  simp only [CollatzResearch.WordTrace]
  refine ⟨208720551432986902968849269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139147034288657935312566179 208720551432986902968849269)
  ·
    refine ⟨19567551696842522153329619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208720551432986902968849269 19567551696842522153329619)
    ·
      refine ⟨29351327545263783229994429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19567551696842522153329619 29351327545263783229994429)
      ·
        refine ⟨11006747829473918711247911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29351327545263783229994429 11006747829473918711247911)
        ·
          refine ⟨16510121744210878066871867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11006747829473918711247911 16510121744210878066871867)
          ·
            refine ⟨24765182616316317100307801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16510121744210878066871867 24765182616316317100307801)
            ·
              refine ⟨18573886962237237825230851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24765182616316317100307801 18573886962237237825230851)
              ·
                refine ⟨27860830443355856737846277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18573886962237237825230851 27860830443355856737846277)
                ·
                  refine ⟨5223905708129223138346177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27860830443355856737846277 5223905708129223138346177)
                  ·
                    refine ⟨3917929281096917353759633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5223905708129223138346177 3917929281096917353759633)
                    ·
                      refine ⟨2938446960822688015319725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3917929281096917353759633 2938446960822688015319725)
                      ·
                        rfl

theorem cell23_5722605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5722605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722605 prefixEnd_5722605 := by exact prefixLift 5722605
  have htrace : WordTrace (prefixWord ++ tailWord_5722605) baseStart_5722605 baseEnd_5722605 := by
    simpa [prefixWord, tailWord_5722605, baseEnd_5722605] using wordTrace_append hprefix tailTrace_5722605
  have hstable : (prefixWord ++ tailWord_5722605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722605).length < 2 ^ (prefixWord ++ tailWord_5722605).sum := by decide
  have hdescent : baseEnd_5722605 < baseStart_5722605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722634 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5722634 : Nat := 118140960795 + 5722634 * 2 ^ 59
def prefixEnd_5722634 : Nat := 4983230072969 + 3 ^ 40 * 5722634 * 2
def baseEnd_5722634 : Nat := 2938461851761668401857091

theorem tailTrace_5722634 : CollatzResearch.WordTrace tailWord_5722634 prefixEnd_5722634 2938461851761668401857091 := by
  unfold tailWord_5722634
  simp only [CollatzResearch.WordTrace]
  refine ⟨52180402287470460230413739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139147739433254560614436637 52180402287470460230413739)
  ·
    refine ⟨78270603431205690345620609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52180402287470460230413739 78270603431205690345620609)
    ·
      refine ⟨58702952573404267759215457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78270603431205690345620609 58702952573404267759215457)
      ·
        refine ⟨44027214430053200819411593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58702952573404267759215457 44027214430053200819411593)
        ·
          refine ⟨33020410822539900614558695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44027214430053200819411593 33020410822539900614558695)
          ·
            refine ⟨49530616233809850921838043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33020410822539900614558695 49530616233809850921838043)
            ·
              refine ⟨74295924350714776382757065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49530616233809850921838043 74295924350714776382757065)
              ·
                refine ⟨55721943263036082287067799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74295924350714776382757065 55721943263036082287067799)
                ·
                  refine ⟨83582914894554123430601699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55721943263036082287067799 83582914894554123430601699)
                  ·
                    refine ⟨125374372341831185145902549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83582914894554123430601699 125374372341831185145902549)
                    ·
                      refine ⟨2938461851761668401857091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125374372341831185145902549 2938461851761668401857091)
                      ·
                        rfl

theorem cell23_5722634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5722634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722634 prefixEnd_5722634 := by exact prefixLift 5722634
  have htrace : WordTrace (prefixWord ++ tailWord_5722634) baseStart_5722634 baseEnd_5722634 := by
    simpa [prefixWord, tailWord_5722634, baseEnd_5722634] using wordTrace_append hprefix tailTrace_5722634
  have hstable : (prefixWord ++ tailWord_5722634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722634).length < 2 ^ (prefixWord ++ tailWord_5722634).sum := by decide
  have hdescent : baseEnd_5722634 < baseStart_5722634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722661 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_5722661 : Nat := 118140960795 + 5722661 * 2 ^ 59
def prefixEnd_5722661 : Nat := 4983230072969 + 3 ^ 40 * 5722661 * 2
def baseEnd_5722661 : Nat := 2938475715739339796219467

theorem tailTrace_5722661 : CollatzResearch.WordTrace tailWord_5722661 prefixEnd_5722661 2938475715739339796219467 := by
  unfold tailWord_5722661
  simp only [CollatzResearch.WordTrace]
  refine ⟨208722593920784024532887837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139148395947189349688591891 208722593920784024532887837)
  ·
    refine ⟨78270972720294009199832939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208722593920784024532887837 78270972720294009199832939)
    ·
      refine ⟨117406459080441013799749409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78270972720294009199832939 117406459080441013799749409)
      ·
        refine ⟨88054844310330760349812057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117406459080441013799749409 88054844310330760349812057)
        ·
          refine ⟨66041133232748070262359043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88054844310330760349812057 66041133232748070262359043)
          ·
            refine ⟨99061699849122105393538565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66041133232748070262359043 99061699849122105393538565)
            ·
              refine ⟨18574068721710394761288481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99061699849122105393538565 18574068721710394761288481)
              ·
                refine ⟨13930551541282796070966361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18574068721710394761288481 13930551541282796070966361)
                ·
                  refine ⟨10447913655962097053224771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13930551541282796070966361 10447913655962097053224771)
                  ·
                    refine ⟨15671870483943145579837157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10447913655962097053224771 15671870483943145579837157)
                    ·
                      refine ⟨2938475715739339796219467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15671870483943145579837157 2938475715739339796219467)
                      ·
                        rfl

theorem cell23_5722661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_5722661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722661 prefixEnd_5722661 := by exact prefixLift 5722661
  have htrace : WordTrace (prefixWord ++ tailWord_5722661) baseStart_5722661 baseEnd_5722661 := by
    simpa [prefixWord, tailWord_5722661, baseEnd_5722661] using wordTrace_append hprefix tailTrace_5722661
  have hstable : (prefixWord ++ tailWord_5722661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722661).length < 2 ^ (prefixWord ++ tailWord_5722661).sum := by decide
  have hdescent : baseEnd_5722661 < baseStart_5722661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722681 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5722681 : Nat := 118140960795 + 5722681 * 2 ^ 59
def prefixEnd_5722681 : Nat := 4983230072969 + 3 ^ 40 * 5722681 * 2
def baseEnd_5722681 : Nat := 2938485985352429717969375

theorem tailTrace_5722681 : CollatzResearch.WordTrace tailWord_5722681 prefixEnd_5722681 2938485985352429717969375 := by
  unfold tailWord_5722681
  simp only [CollatzResearch.WordTrace]
  refine ⟨208723323380711567948615897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139148882253807711965743931 208723323380711567948615897)
  ·
    refine ⟨156542492535533675961461923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208723323380711567948615897 156542492535533675961461923)
    ·
      refine ⟨234813738803300513942192885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156542492535533675961461923 234813738803300513942192885)
      ·
        refine ⟨22013788012809423182080583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234813738803300513942192885 22013788012809423182080583)
        ·
          refine ⟨33020682019214134773120875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22013788012809423182080583 33020682019214134773120875)
          ·
            refine ⟨49531023028821202159681313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33020682019214134773120875 49531023028821202159681313)
            ·
              refine ⟨37148267271615901619760985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49531023028821202159681313 37148267271615901619760985)
              ·
                refine ⟨27861200453711926214820739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37148267271615901619760985 27861200453711926214820739)
                ·
                  refine ⟨41791800680567889322231109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27861200453711926214820739 41791800680567889322231109)
                  ·
                    refine ⟨7835962627606479247918333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41791800680567889322231109 7835962627606479247918333)
                    ·
                      refine ⟨2938485985352429717969375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7835962627606479247918333 2938485985352429717969375)
                      ·
                        rfl

theorem cell23_5722681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5722681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722681 prefixEnd_5722681 := by exact prefixLift 5722681
  have htrace : WordTrace (prefixWord ++ tailWord_5722681) baseStart_5722681 baseEnd_5722681 := by
    simpa [prefixWord, tailWord_5722681, baseEnd_5722681] using wordTrace_append hprefix tailTrace_5722681
  have hstable : (prefixWord ++ tailWord_5722681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722681).length < 2 ^ (prefixWord ++ tailWord_5722681).sum := by decide
  have hdescent : baseEnd_5722681 < baseStart_5722681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722698 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_5722698 : Nat := 118140960795 + 5722698 * 2 ^ 59
def prefixEnd_5722698 : Nat := 4983230072969 + 3 ^ 40 * 5722698 * 2
def baseEnd_5722698 : Nat := 2938494714523556151456797

theorem tailTrace_5722698 : CollatzResearch.WordTrace tailWord_5722698 prefixEnd_5722698 2938494714523556151456797 := by
  unfold tailWord_5722698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52180985855412494962996187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139149295614433319901323165 52180985855412494962996187)
  ·
    refine ⟨78271478783118742444494281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52180985855412494962996187 78271478783118742444494281)
    ·
      refine ⟨58703609087339056833370711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78271478783118742444494281 58703609087339056833370711)
      ·
        refine ⟨88055413631008585250056067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58703609087339056833370711 88055413631008585250056067)
        ·
          refine ⟨132083120446512877875084101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88055413631008585250056067 132083120446512877875084101)
          ·
            refine ⟨24765585083721164601578269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132083120446512877875084101 24765585083721164601578269)
            ·
              refine ⟨9287094406395436725591851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24765585083721164601578269 9287094406395436725591851)
              ·
                refine ⟨13930641609593155088387777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287094406395436725591851 13930641609593155088387777)
                ·
                  refine ⟨10447981207194866316290833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13930641609593155088387777 10447981207194866316290833)
                  ·
                    refine ⟨7835985905396149737218125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10447981207194866316290833 7835985905396149737218125)
                    ·
                      refine ⟨2938494714523556151456797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7835985905396149737218125 2938494714523556151456797)
                      ·
                        rfl

theorem cell23_5722698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_5722698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722698 prefixEnd_5722698 := by exact prefixLift 5722698
  have htrace : WordTrace (prefixWord ++ tailWord_5722698) baseStart_5722698 baseEnd_5722698 := by
    simpa [prefixWord, tailWord_5722698, baseEnd_5722698] using wordTrace_append hprefix tailTrace_5722698
  have hstable : (prefixWord ++ tailWord_5722698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722698).length < 2 ^ (prefixWord ++ tailWord_5722698).sum := by decide
  have hdescent : baseEnd_5722698 < baseStart_5722698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722705 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 1, 4]
def baseStart_5722705 : Nat := 118140960795 + 5722705 * 2 ^ 59
def prefixEnd_5722705 : Nat := 4983230072969 + 3 ^ 40 * 5722705 * 2
def baseEnd_5722705 : Nat := 979499436296045874689755

theorem tailTrace_5722705 : CollatzResearch.WordTrace tailWord_5722705 prefixEnd_5722705 979499436296045874689755 := by
  unfold tailWord_5722705
  simp only [CollatzResearch.WordTrace]
  refine ⟨208724198732624620047489569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139149465821749746698326379 208724198732624620047489569)
  ·
    refine ⟨156543149049468465035617177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208724198732624620047489569 156543149049468465035617177)
    ·
      refine ⟨117407361787101348776712883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156543149049468465035617177 117407361787101348776712883)
      ·
        refine ⟨176111042680652023165069325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117407361787101348776712883 176111042680652023165069325)
        ·
          refine ⟨66041641005244508686900997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176111042680652023165069325 66041641005244508686900997)
          ·
            refine ⟨12382807688483345378793937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66041641005244508686900997 12382807688483345378793937)
            ·
              refine ⟨9287105766362509034095453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382807688483345378793937 9287105766362509034095453)
              ·
                refine ⟨3482664662385940887785795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9287105766362509034095453 3482664662385940887785795)
                ·
                  refine ⟨5223996993578911331678693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482664662385940887785795 5223996993578911331678693)
                  ·
                    refine ⟨979499436296045874689755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5223996993578911331678693 979499436296045874689755)
                    ·
                      rfl

theorem cell23_5722705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_5722705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722705 prefixEnd_5722705 := by exact prefixLift 5722705
  have htrace : WordTrace (prefixWord ++ tailWord_5722705) baseStart_5722705 baseEnd_5722705 := by
    simpa [prefixWord, tailWord_5722705, baseEnd_5722705] using wordTrace_append hprefix tailTrace_5722705
  have hstable : (prefixWord ++ tailWord_5722705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722705).length < 2 ^ (prefixWord ++ tailWord_5722705).sum := by decide
  have hdescent : baseEnd_5722705 < baseStart_5722705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722722 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_5722722 : Nat := 118140960795 + 5722722 * 2 ^ 59
def prefixEnd_5722722 : Nat := 4983230072969 + 3 ^ 40 * 5722722 * 2
def baseEnd_5722722 : Nat := 979502346019754685852229

theorem tailTrace_5722722 : CollatzResearch.WordTrace tailWord_5722722 prefixEnd_5722722 979502346019754685852229 := by
  unfold tailWord_5722722
  simp only [CollatzResearch.WordTrace]
  refine ⟨52181204693390757987714605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139149879182375354633905613 52181204693390757987714605)
  ·
    refine ⟨19567951760021534245392977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52181204693390757987714605 19567951760021534245392977)
    ·
      refine ⟨14675963820016150684044733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19567951760021534245392977 14675963820016150684044733)
      ·
        refine ⟨5503486432506056506516775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14675963820016150684044733 5503486432506056506516775)
        ·
          refine ⟨8255229648759084759775163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503486432506056506516775 8255229648759084759775163)
          ·
            refine ⟨12382844473138627139662745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255229648759084759775163 12382844473138627139662745)
            ·
              refine ⟨9287133354853970354747059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382844473138627139662745 9287133354853970354747059)
              ·
                refine ⟨13930700032280955532120589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287133354853970354747059 13930700032280955532120589)
                ·
                  refine ⟨5224012512105358324545221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13930700032280955532120589 5224012512105358324545221)
                  ·
                    refine ⟨979502346019754685852229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5224012512105358324545221 979502346019754685852229)
                    ·
                      rfl

theorem cell23_5722722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_5722722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722722 prefixEnd_5722722 := by exact prefixLift 5722722
  have htrace : WordTrace (prefixWord ++ tailWord_5722722) baseStart_5722722 baseEnd_5722722 := by
    simpa [prefixWord, tailWord_5722722, baseEnd_5722722] using wordTrace_append hprefix tailTrace_5722722
  have hstable : (prefixWord ++ tailWord_5722722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722722).length < 2 ^ (prefixWord ++ tailWord_5722722).sum := by decide
  have hdescent : baseEnd_5722722 < baseStart_5722722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722772 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5722772 : Nat := 118140960795 + 5722772 * 2 ^ 59
def prefixEnd_5722772 : Nat := 4983230072969 + 3 ^ 40 * 5722772 * 2
def baseEnd_5722772 : Nat := 2938532712091988861931457

theorem tailTrace_5722772 : CollatzResearch.WordTrace tailWord_5722772 prefixEnd_5722772 2938532712091988861931457 := by
  unfold tailWord_5722772
  simp only [CollatzResearch.WordTrace]
  refine ⟨104363321211690945245089285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139151094948921260326785713 104363321211690945245089285)
  ·
    refine ⟨19568122727192052233454241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104363321211690945245089285 19568122727192052233454241)
    ·
      refine ⟨14676092045394039175090681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19568122727192052233454241 14676092045394039175090681)
      ·
        refine ⟨11007069034045529381318011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14676092045394039175090681 11007069034045529381318011)
        ·
          refine ⟨16510603551068294071977017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11007069034045529381318011 16510603551068294071977017)
          ·
            refine ⟨12382952663301220553982763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16510603551068294071977017 12382952663301220553982763)
            ·
              refine ⟨18574428994951830830974145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12382952663301220553982763 18574428994951830830974145)
              ·
                refine ⟨13930821746213873123230609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18574428994951830830974145 13930821746213873123230609)
                ·
                  refine ⟨10448116309660404842422957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13930821746213873123230609 10448116309660404842422957)
                  ·
                    refine ⟨3918043616122651815908609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10448116309660404842422957 3918043616122651815908609)
                    ·
                      refine ⟨2938532712091988861931457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918043616122651815908609 2938532712091988861931457)
                      ·
                        rfl

theorem cell23_5722772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5722772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722772 prefixEnd_5722772 := by exact prefixLift 5722772
  have htrace : WordTrace (prefixWord ++ tailWord_5722772) baseStart_5722772 baseEnd_5722772 := by
    simpa [prefixWord, tailWord_5722772, baseEnd_5722772] using wordTrace_append hprefix tailTrace_5722772
  have hstable : (prefixWord ++ tailWord_5722772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722772).length < 2 ^ (prefixWord ++ tailWord_5722772).sum := by decide
  have hdescent : baseEnd_5722772 < baseStart_5722772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722781 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5722781 : Nat := 118140960795 + 5722781 * 2 ^ 59
def prefixEnd_5722781 : Nat := 4983230072969 + 3 ^ 40 * 5722781 * 2
def baseEnd_5722781 : Nat := 2938537333417879326718915

theorem tailTrace_5722781 : CollatzResearch.WordTrace tailWord_5722781 prefixEnd_5722781 2938537333417879326718915 := by
  unfold tailWord_5722781
  simp only [CollatzResearch.WordTrace]
  refine ⟨208726970680349285027256197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139151313786899523351504131 208726970680349285027256197)
  ·
    refine ⟨39136307002565490942610537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208726970680349285027256197 39136307002565490942610537)
    ·
      refine ⟨29352230251924118206957903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39136307002565490942610537 29352230251924118206957903)
      ·
        refine ⟨44028345377886177310436855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29352230251924118206957903 44028345377886177310436855)
        ·
          refine ⟨66042518066829265965655283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44028345377886177310436855 66042518066829265965655283)
          ·
            refine ⟨99063777100243898948482925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66042518066829265965655283 99063777100243898948482925)
            ·
              refine ⟨37148916412591462105681097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99063777100243898948482925 37148916412591462105681097)
              ·
                refine ⟨27861687309443596579260823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37148916412591462105681097 27861687309443596579260823)
                ·
                  refine ⟨41792530964165394868891235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27861687309443596579260823 41792530964165394868891235)
                  ·
                    refine ⟨62688796446248092303336853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41792530964165394868891235 62688796446248092303336853)
                    ·
                      refine ⟨2938537333417879326718915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62688796446248092303336853 2938537333417879326718915)
                      ·
                        rfl

theorem cell23_5722781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5722781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722781 prefixEnd_5722781 := by exact prefixLift 5722781
  have htrace : WordTrace (prefixWord ++ tailWord_5722781) baseStart_5722781 baseEnd_5722781 := by
    simpa [prefixWord, tailWord_5722781, baseEnd_5722781] using wordTrace_append hprefix tailTrace_5722781
  have hstable : (prefixWord ++ tailWord_5722781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722781).length < 2 ^ (prefixWord ++ tailWord_5722781).sum := by decide
  have hdescent : baseEnd_5722781 < baseStart_5722781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722788 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_5722788 : Nat := 118140960795 + 5722788 * 2 ^ 59
def prefixEnd_5722788 : Nat := 4983230072969 + 3 ^ 40 * 5722788 * 2
def baseEnd_5722788 : Nat := 2938540927782460799331383

theorem tailTrace_5722788 : CollatzResearch.WordTrace tailWord_5722788 prefixEnd_5722788 2938540927782460799331383 := by
  unfold tailWord_5722788
  simp only [CollatzResearch.WordTrace]
  refine ⟨104363612995661962611380509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139151483994215950148507345 104363612995661962611380509)
  ·
    refine ⟨39136354873373235979267691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104363612995661962611380509 39136354873373235979267691)
    ·
      refine ⟨58704532310059853968901537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39136354873373235979267691 58704532310059853968901537)
      ·
        refine ⟨44028399232544890476676153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58704532310059853968901537 44028399232544890476676153)
        ·
          refine ⟨33021299424408667857507115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44028399232544890476676153 33021299424408667857507115)
          ·
            refine ⟨49531949136613001786260673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33021299424408667857507115 49531949136613001786260673)
            ·
              refine ⟨37148961852459751339695505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49531949136613001786260673 37148961852459751339695505)
              ·
                refine ⟨27861721389344813504771629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37148961852459751339695505 27861721389344813504771629)
                ·
                  refine ⟨10448145521004305064289361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27861721389344813504771629 10448145521004305064289361)
                  ·
                    refine ⟨7836109140753228798217021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10448145521004305064289361 7836109140753228798217021)
                    ·
                      refine ⟨2938540927782460799331383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836109140753228798217021 2938540927782460799331383)
                      ·
                        rfl

theorem cell23_5722788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_5722788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722788 prefixEnd_5722788 := by exact prefixLift 5722788
  have htrace : WordTrace (prefixWord ++ tailWord_5722788) baseStart_5722788 baseEnd_5722788 := by
    simpa [prefixWord, tailWord_5722788, baseEnd_5722788] using wordTrace_append hprefix tailTrace_5722788
  have hstable : (prefixWord ++ tailWord_5722788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722788).length < 2 ^ (prefixWord ++ tailWord_5722788).sum := by decide
  have hdescent : baseEnd_5722788 < baseStart_5722788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722805 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_5722805 : Nat := 118140960795 + 5722805 * 2 ^ 59
def prefixEnd_5722805 : Nat := 4983230072969 + 3 ^ 40 * 5722805 * 2
def baseEnd_5722805 : Nat := 2938549656953587232818805

theorem tailTrace_5722805 : CollatzResearch.WordTrace tailWord_5722805 prefixEnd_5722805 2938549656953587232818805 := by
  unfold tailWord_5722805
  simp only [CollatzResearch.WordTrace]
  refine ⟨208727846032262337126129869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139151897354841558084086579 208727846032262337126129869)
  ·
    refine ⟨78272942262098376422298701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208727846032262337126129869 78272942262098376422298701)
    ·
      refine ⟨29352353348286891158362013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78272942262098376422298701 29352353348286891158362013)
      ·
        refine ⟨11007132505607584184385755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29352353348286891158362013 11007132505607584184385755)
        ·
          refine ⟨16510698758411376276578633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11007132505607584184385755 16510698758411376276578633)
          ·
            refine ⟨12383024068808532207433975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16510698758411376276578633 12383024068808532207433975)
            ·
              refine ⟨18574536103212798311150963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12383024068808532207433975 18574536103212798311150963)
              ·
                refine ⟨27861804154819197466726445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18574536103212798311150963 27861804154819197466726445)
                ·
                  refine ⟨10448176558057199050022417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27861804154819197466726445 10448176558057199050022417)
                  ·
                    refine ⟨7836132418542899287516813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10448176558057199050022417 7836132418542899287516813)
                    ·
                      refine ⟨2938549656953587232818805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836132418542899287516813 2938549656953587232818805)
                      ·
                        rfl

theorem cell23_5722805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_5722805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722805 prefixEnd_5722805 := by exact prefixLift 5722805
  have htrace : WordTrace (prefixWord ++ tailWord_5722805) baseStart_5722805 baseEnd_5722805 := by
    simpa [prefixWord, tailWord_5722805, baseEnd_5722805] using wordTrace_append hprefix tailTrace_5722805
  have hstable : (prefixWord ++ tailWord_5722805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722805).length < 2 ^ (prefixWord ++ tailWord_5722805).sum := by decide
  have hdescent : baseEnd_5722805 < baseStart_5722805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722829 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5722829 : Nat := 118140960795 + 5722829 * 2 ^ 59
def prefixEnd_5722829 : Nat := 4983230072969 + 3 ^ 40 * 5722829 * 2
def baseEnd_5722829 : Nat := 979520660163098379639565

theorem tailTrace_5722829 : CollatzResearch.WordTrace tailWord_5722829 prefixEnd_5722829 979520660163098379639565 := by
  unfold tailWord_5722829
  simp only [CollatzResearch.WordTrace]
  refine ⟨208728721384175389225003541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139152480922783592816669027 208728721384175389225003541)
  ·
    refine ⟨9784158814883221369922041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208728721384175389225003541 9784158814883221369922041)
    ·
      refine ⟨7338119111162416027441531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9784158814883221369922041 7338119111162416027441531)
      ·
        refine ⟨11007178666743624041162297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7338119111162416027441531 11007178666743624041162297)
        ·
          refine ⟨8255384000057718030871723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11007178666743624041162297 8255384000057718030871723)
          ·
            refine ⟨12383076000086577046307585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255384000057718030871723 12383076000086577046307585)
            ·
              refine ⟨9287307000064932784730689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12383076000086577046307585 9287307000064932784730689)
              ·
                refine ⟨6965480250048699588548017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9287307000064932784730689 6965480250048699588548017)
                ·
                  refine ⟨5224110187536524691411013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6965480250048699588548017 5224110187536524691411013)
                  ·
                    refine ⟨979520660163098379639565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5224110187536524691411013 979520660163098379639565)
                    ·
                      rfl

theorem cell23_5722829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5722829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722829 prefixEnd_5722829 := by exact prefixLift 5722829
  have htrace : WordTrace (prefixWord ++ tailWord_5722829) baseStart_5722829 baseEnd_5722829 := by
    simpa [prefixWord, tailWord_5722829, baseEnd_5722829] using wordTrace_append hprefix tailTrace_5722829
  have hstable : (prefixWord ++ tailWord_5722829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722829).length < 2 ^ (prefixWord ++ tailWord_5722829).sum := by decide
  have hdescent : baseEnd_5722829 < baseStart_5722829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722836 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5722836 : Nat := 118140960795 + 5722836 * 2 ^ 59
def prefixEnd_5722836 : Nat := 4983230072969 + 3 ^ 40 * 5722836 * 2
def baseEnd_5722836 : Nat := 2938565574853876611531163

theorem tailTrace_5722836 : CollatzResearch.WordTrace tailWord_5722836 prefixEnd_5722836 2938565574853876611531163 := by
  unfold tailWord_5722836
  simp only [CollatzResearch.WordTrace]
  refine ⟨104364488347575014710254181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139152651130100019613672241 104364488347575014710254181)
  ·
    refine ⟨19568341565170315258172659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104364488347575014710254181 19568341565170315258172659)
    ·
      refine ⟨29352512347755472887258989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19568341565170315258172659 29352512347755472887258989)
      ·
        refine ⟨11007192130408302332722121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29352512347755472887258989 11007192130408302332722121)
        ·
          refine ⟨8255394097806226749541591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11007192130408302332722121 8255394097806226749541591)
          ·
            refine ⟨12383091146709340124312387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255394097806226749541591 12383091146709340124312387)
            ·
              refine ⟨18574636720064010186468581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12383091146709340124312387 18574636720064010186468581)
              ·
                refine ⟨3482744385012001909962859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18574636720064010186468581 3482744385012001909962859)
                ·
                  refine ⟨5224116577518002864944289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482744385012001909962859 5224116577518002864944289)
                  ·
                    refine ⟨3918087433138502148708217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5224116577518002864944289 3918087433138502148708217)
                    ·
                      refine ⟨2938565574853876611531163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918087433138502148708217 2938565574853876611531163)
                      ·
                        rfl

theorem cell23_5722836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5722836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722836 prefixEnd_5722836 := by exact prefixLift 5722836
  have htrace : WordTrace (prefixWord ++ tailWord_5722836) baseStart_5722836 baseEnd_5722836 := by
    simpa [prefixWord, tailWord_5722836, baseEnd_5722836] using wordTrace_append hprefix tailTrace_5722836
  have hstable : (prefixWord ++ tailWord_5722836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722836).length < 2 ^ (prefixWord ++ tailWord_5722836).sum := by decide
  have hdescent : baseEnd_5722836 < baseStart_5722836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722841 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_5722841 : Nat := 118140960795 + 5722841 * 2 ^ 59
def prefixEnd_5722841 : Nat := 4983230072969 + 3 ^ 40 * 5722841 * 2
def baseEnd_5722841 : Nat := 2938568142257149091968639

theorem tailTrace_5722841 : CollatzResearch.WordTrace tailWord_5722841 prefixEnd_5722841 2938568142257149091968639 := by
  unfold tailWord_5722841
  simp only [CollatzResearch.WordTrace]
  refine ⟨208729159060131915274440377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139152772706754610182960251 208729159060131915274440377)
  ·
    refine ⟨156546869295098936455830283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208729159060131915274440377 156546869295098936455830283)
    ·
      refine ⟨234820303942648404683745425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156546869295098936455830283 234820303942648404683745425)
      ·
        refine ⟨176115227956986303512809069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234820303942648404683745425 176115227956986303512809069)
        ·
          refine ⟨66043210483869863817303401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176115227956986303512809069 66043210483869863817303401)
          ·
            refine ⟨49532407862902397862977551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66043210483869863817303401 49532407862902397862977551)
            ·
              refine ⟨74298611794353596794466327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49532407862902397862977551 74298611794353596794466327)
              ·
                refine ⟨111447917691530395191699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74298611794353596794466327 111447917691530395191699491)
                ·
                  refine ⟨167171876537295592787549237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111447917691530395191699491 167171876537295592787549237)
                  ·
                    refine ⟨15672363425371461823832741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 167171876537295592787549237 15672363425371461823832741)
                    ·
                      refine ⟨2938568142257149091968639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15672363425371461823832741 2938568142257149091968639)
                      ·
                        rfl

theorem cell23_5722841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_5722841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722841 prefixEnd_5722841 := by exact prefixLift 5722841
  have htrace : WordTrace (prefixWord ++ tailWord_5722841) baseStart_5722841 baseEnd_5722841 := by
    simpa [prefixWord, tailWord_5722841, baseEnd_5722841] using wordTrace_append hprefix tailTrace_5722841
  have hstable : (prefixWord ++ tailWord_5722841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722841).length < 2 ^ (prefixWord ++ tailWord_5722841).sum := by decide
  have hdescent : baseEnd_5722841 < baseStart_5722841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722871 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_5722871 : Nat := 118140960795 + 5722871 * 2 ^ 59
def prefixEnd_5722871 : Nat := 4983230072969 + 3 ^ 40 * 5722871 * 2
def baseEnd_5722871 : Nat := 2938583546676783974593501

theorem tailTrace_5722871 : CollatzResearch.WordTrace tailWord_5722871 prefixEnd_5722871 2938583546676783974593501 := by
  unfold tailWord_5722871
  simp only [CollatzResearch.WordTrace]
  refine ⟨208730253250023230398032467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139153502166682153598688311 208730253250023230398032467)
  ·
    refine ⟨313095379875034845597048701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208730253250023230398032467 313095379875034845597048701)
    ·
      refine ⟨117410767453138067098893263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313095379875034845597048701 117410767453138067098893263)
      ·
        refine ⟨176116151179707100648339895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117410767453138067098893263 176116151179707100648339895)
        ·
          refine ⟨264174226769560650972509843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176116151179707100648339895 264174226769560650972509843)
          ·
            refine ⟨396261340154340976458764765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264174226769560650972509843 396261340154340976458764765)
            ·
              refine ⟨148598002557877866172036787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396261340154340976458764765 148598002557877866172036787)
              ·
                refine ⟨222897003836816799258055181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148598002557877866172036787 222897003836816799258055181)
                ·
                  refine ⟨83586376438806299721770693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222897003836816799258055181 83586376438806299721770693)
                  ·
                    refine ⟨15672445582276181197832005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83586376438806299721770693 15672445582276181197832005)
                    ·
                      refine ⟨2938583546676783974593501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15672445582276181197832005 2938583546676783974593501)
                      ·
                        rfl

theorem cell23_5722871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_5722871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722871 prefixEnd_5722871 := by exact prefixLift 5722871
  have htrace : WordTrace (prefixWord ++ tailWord_5722871) baseStart_5722871 baseEnd_5722871 := by
    simpa [prefixWord, tailWord_5722871, baseEnd_5722871] using wordTrace_append hprefix tailTrace_5722871
  have hstable : (prefixWord ++ tailWord_5722871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722871).length < 2 ^ (prefixWord ++ tailWord_5722871).sum := by decide
  have hdescent : baseEnd_5722871 < baseStart_5722871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722881 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 11]
def baseStart_5722881 : Nat := 118140960795 + 5722881 * 2 ^ 59
def prefixEnd_5722881 : Nat := 4983230072969 + 3 ^ 40 * 5722881 * 2
def baseEnd_5722881 : Nat := 326509853498147659496495

theorem tailTrace_5722881 : CollatzResearch.WordTrace tailWord_5722881 prefixEnd_5722881 326509853498147659496495 := by
  unfold tailWord_5722881
  simp only [CollatzResearch.WordTrace]
  refine ⟨208730617979987002105896497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139153745319991334737264331 208730617979987002105896497)
  ·
    refine ⟨156547963484990251579422373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208730617979987002105896497 156547963484990251579422373)
    ·
      refine ⟨29352743153435672171141695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156547963484990251579422373 29352743153435672171141695)
      ·
        refine ⟨44029114730153508256712543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29352743153435672171141695 44029114730153508256712543)
        ·
          refine ⟨66043672095230262385068815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44029114730153508256712543 66043672095230262385068815)
          ·
            refine ⟨99065508142845393577603223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66043672095230262385068815 99065508142845393577603223)
            ·
              refine ⟨148598262214268090366404835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99065508142845393577603223 148598262214268090366404835)
              ·
                refine ⟨222897393321402135549607253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148598262214268090366404835 222897393321402135549607253)
                ·
                  refine ⟨326509853498147659496495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 222897393321402135549607253 326509853498147659496495)
                  ·
                    rfl

theorem cell23_5722881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_5722881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722881 prefixEnd_5722881 := by exact prefixLift 5722881
  have htrace : WordTrace (prefixWord ++ tailWord_5722881) baseStart_5722881 baseEnd_5722881 := by
    simpa [prefixWord, tailWord_5722881, baseEnd_5722881] using wordTrace_append hprefix tailTrace_5722881
  have hstable : (prefixWord ++ tailWord_5722881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722881).length < 2 ^ (prefixWord ++ tailWord_5722881).sum := by decide
  have hdescent : baseEnd_5722881 < baseStart_5722881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722888 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5722888 : Nat := 118140960795 + 5722888 * 2 ^ 59
def prefixEnd_5722888 : Nat := 4983230072969 + 3 ^ 40 * 5722888 * 2
def baseEnd_5722888 : Nat := 2938592275847910408080923

theorem tailTrace_5722888 : CollatzResearch.WordTrace tailWord_5722888 prefixEnd_5722888 2938592275847910408080923 := by
  unfold tailWord_5722888
  simp only [CollatzResearch.WordTrace]
  refine ⟨104365436645480821150700659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139153915527307761534267545 104365436645480821150700659)
  ·
    refine ⟨156548154968221231726050989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104365436645480821150700659 156548154968221231726050989)
    ·
      refine ⟨58705558113082961897269121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156548154968221231726050989 58705558113082961897269121)
      ·
        refine ⟨44029168584812221422951841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58705558113082961897269121 44029168584812221422951841)
        ·
          refine ⟨33021876438609166067213881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44029168584812221422951841 33021876438609166067213881)
          ·
            refine ⟨24766407328956874550410411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33021876438609166067213881 24766407328956874550410411)
            ·
              refine ⟨37149610993435311825615617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24766407328956874550410411 37149610993435311825615617)
              ·
                refine ⟨27862208245076483869211713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37149610993435311825615617 27862208245076483869211713)
                ·
                  refine ⟨20896656183807362901908785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27862208245076483869211713 20896656183807362901908785)
                  ·
                    refine ⟨15672492137855522176431589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20896656183807362901908785 15672492137855522176431589)
                    ·
                      refine ⟨2938592275847910408080923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15672492137855522176431589 2938592275847910408080923)
                      ·
                        rfl

theorem cell23_5722888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5722888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722888 prefixEnd_5722888 := by exact prefixLift 5722888
  have htrace : WordTrace (prefixWord ++ tailWord_5722888) baseStart_5722888 baseEnd_5722888 := by
    simpa [prefixWord, tailWord_5722888, baseEnd_5722888] using wordTrace_append hprefix tailTrace_5722888
  have hstable : (prefixWord ++ tailWord_5722888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722888).length < 2 ^ (prefixWord ++ tailWord_5722888).sum := by decide
  have hdescent : baseEnd_5722888 < baseStart_5722888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722921 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_5722921 : Nat := 118140960795 + 5722921 * 2 ^ 59
def prefixEnd_5722921 : Nat := 4983230072969 + 3 ^ 40 * 5722921 * 2
def baseEnd_5722921 : Nat := 2938609220709508778968271

theorem tailTrace_5722921 : CollatzResearch.WordTrace tailWord_5722921 prefixEnd_5722921 2938609220709508778968271 := by
  unfold tailWord_5722921
  simp only [CollatzResearch.WordTrace]
  refine ⟨208732076899842088937352617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139154717933228059291568411 208732076899842088937352617)
  ·
    refine ⟨156549057674881566703014463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208732076899842088937352617 156549057674881566703014463)
    ·
      refine ⟨234823586512322350054521695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156549057674881566703014463 234823586512322350054521695)
      ·
        refine ⟨352235379768483525081782543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234823586512322350054521695 352235379768483525081782543)
        ·
          refine ⟨528353069652725287622673815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352235379768483525081782543 528353069652725287622673815)
          ·
            refine ⟨792529604479087931434010723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528353069652725287622673815 792529604479087931434010723)
            ·
              refine ⟨1188794406718631897151016085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792529604479087931434010723 1188794406718631897151016085)
              ·
                refine ⟨55724737814935870178953879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1188794406718631897151016085 55724737814935870178953879)
                ·
                  refine ⟨83587106722403805268430819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55724737814935870178953879 83587106722403805268430819)
                  ·
                    refine ⟨125380660083605707902646229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83587106722403805268430819 125380660083605707902646229)
                    ·
                      refine ⟨2938609220709508778968271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125380660083605707902646229 2938609220709508778968271)
                      ·
                        rfl

theorem cell23_5722921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_5722921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722921 prefixEnd_5722921 := by exact prefixLift 5722921
  have htrace : WordTrace (prefixWord ++ tailWord_5722921) baseStart_5722921 baseEnd_5722921 := by
    simpa [prefixWord, tailWord_5722921, baseEnd_5722921] using wordTrace_append hprefix tailTrace_5722921
  have hstable : (prefixWord ++ tailWord_5722921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722921).length < 2 ^ (prefixWord ++ tailWord_5722921).sum := by decide
  have hdescent : baseEnd_5722921 < baseStart_5722921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722965 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_5722965 : Nat := 118140960795 + 5722965 * 2 ^ 59
def prefixEnd_5722965 : Nat := 4983230072969 + 3 ^ 40 * 5722965 * 2
def baseEnd_5722965 : Nat := 2938631813858306606818069

theorem tailTrace_5722965 : CollatzResearch.WordTrace tailWord_5722965 prefixEnd_5722965 2938631813858306606818069 := by
  unfold tailWord_5722965
  simp only [CollatzResearch.WordTrace]
  refine ⟨208733681711682684451954349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139155787807788456301302899 208733681711682684451954349)
  ·
    refine ⟨78275130641881006669482881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208733681711682684451954349 78275130641881006669482881)
    ·
      refine ⟨58706347981410755002112161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78275130641881006669482881 58706347981410755002112161)
      ·
        refine ⟨44029760986058066251584121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58706347981410755002112161 44029760986058066251584121)
        ·
          refine ⟨33022320739543549688688091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44029760986058066251584121 33022320739543549688688091)
          ·
            refine ⟨49533481109315324533032137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33022320739543549688688091 49533481109315324533032137)
            ·
              refine ⟨37150110831986493399774103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49533481109315324533032137 37150110831986493399774103)
              ·
                refine ⟨55725166247979740099661155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37150110831986493399774103 55725166247979740099661155)
                ·
                  refine ⟨83587749371969610149491733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55725166247979740099661155 83587749371969610149491733)
                  ·
                    refine ⟨3918175751811075475757425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83587749371969610149491733 3918175751811075475757425)
                    ·
                      refine ⟨2938631813858306606818069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918175751811075475757425 2938631813858306606818069)
                      ·
                        rfl

theorem cell23_5722965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_5722965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722965 prefixEnd_5722965 := by exact prefixLift 5722965
  have htrace : WordTrace (prefixWord ++ tailWord_5722965) baseStart_5722965 baseEnd_5722965 := by
    simpa [prefixWord, tailWord_5722965, baseEnd_5722965] using wordTrace_append hprefix tailTrace_5722965
  have hstable : (prefixWord ++ tailWord_5722965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722965).length < 2 ^ (prefixWord ++ tailWord_5722965).sum := by decide
  have hdescent : baseEnd_5722965 < baseStart_5722965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5722968 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_5722968 : Nat := 118140960795 + 5722968 * 2 ^ 59
def prefixEnd_5722968 : Nat := 4983230072969 + 3 ^ 40 * 5722968 * 2
def baseEnd_5722968 : Nat := 2938633354300270095080555

theorem tailTrace_5722968 : CollatzResearch.WordTrace tailWord_5722968 prefixEnd_5722968 2938633354300270095080555 := by
  unfold tailWord_5722968
  simp only [CollatzResearch.WordTrace]
  refine ⟨104366895565335907982156779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139155860753781210642875705 104366895565335907982156779)
  ·
    refine ⟨156550343348003861973235169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104366895565335907982156779 156550343348003861973235169)
    ·
      refine ⟨117412757511002896479926377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156550343348003861973235169 117412757511002896479926377)
      ·
        refine ⟨88059568133252172359944783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117412757511002896479926377 88059568133252172359944783)
        ·
          refine ⟨132089352199878258539917175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88059568133252172359944783 132089352199878258539917175)
          ·
            refine ⟨198134028299817387809875763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132089352199878258539917175 198134028299817387809875763)
            ·
              refine ⟨297201042449726081714813645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198134028299817387809875763 297201042449726081714813645)
              ·
                refine ⟨111450390918647280643055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297201042449726081714813645 111450390918647280643055117)
                ·
                  refine ⟨41793896594492730241145669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111450390918647280643055117 41793896594492730241145669)
                  ·
                    refine ⟨7836355611467386920214813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41793896594492730241145669 7836355611467386920214813)
                    ·
                      refine ⟨2938633354300270095080555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836355611467386920214813 2938633354300270095080555)
                      ·
                        rfl

theorem cell23_5722968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_5722968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5722968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5722968 prefixEnd_5722968 := by exact prefixLift 5722968
  have htrace : WordTrace (prefixWord ++ tailWord_5722968) baseStart_5722968 baseEnd_5722968 := by
    simpa [prefixWord, tailWord_5722968, baseEnd_5722968] using wordTrace_append hprefix tailTrace_5722968
  have hstable : (prefixWord ++ tailWord_5722968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5722968).length < 2 ^ (prefixWord ++ tailWord_5722968).sum := by decide
  have hdescent : baseEnd_5722968 < baseStart_5722968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5722968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723025 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 1, 5, 2]
def baseStart_5723025 : Nat := 118140960795 + 5723025 * 2 ^ 59
def prefixEnd_5723025 : Nat := 4983230072969 + 3 ^ 40 * 5723025 * 2
def baseEnd_5723025 : Nat := 2938662622697576372067793

theorem tailTrace_5723025 : CollatzResearch.WordTrace tailWord_5723025 prefixEnd_5723025 2938662622697576372067793 := by
  unfold tailWord_5723025
  simp only [CollatzResearch.WordTrace]
  refine ⟨208735870091465314699138529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139157246727643543132759019 208735870091465314699138529)
  ·
    refine ⟨156551902568598986024353897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208735870091465314699138529 156551902568598986024353897)
    ·
      refine ⟨117413926926449239518265423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156551902568598986024353897 117413926926449239518265423)
      ·
        refine ⟨176120890389673859277398135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117413926926449239518265423 176120890389673859277398135)
        ·
          refine ⟨264181335584510788916097203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176120890389673859277398135 264181335584510788916097203)
          ·
            refine ⟨396272003376766183374145805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264181335584510788916097203 396272003376766183374145805)
            ·
              refine ⟨148602001266287318765304677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396272003376766183374145805 148602001266287318765304677)
              ·
                refine ⟨27862875237428872268494627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148602001266287318765304677 27862875237428872268494627)
                ·
                  refine ⟨41794312856143308402741941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27862875237428872268494627 41794312856143308402741941)
                  ·
                    refine ⟨3918216830263435162757057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41794312856143308402741941 3918216830263435162757057)
                    ·
                      refine ⟨2938662622697576372067793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918216830263435162757057 2938662622697576372067793)
                      ·
                        rfl

theorem cell23_5723025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_5723025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723025 prefixEnd_5723025 := by exact prefixLift 5723025
  have htrace : WordTrace (prefixWord ++ tailWord_5723025) baseStart_5723025 baseEnd_5723025 := by
    simpa [prefixWord, tailWord_5723025, baseEnd_5723025] using wordTrace_append hprefix tailTrace_5723025
  have hstable : (prefixWord ++ tailWord_5723025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723025).length < 2 ^ (prefixWord ++ tailWord_5723025).sum := by decide
  have hdescent : baseEnd_5723025 < baseStart_5723025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723036 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5723036 : Nat := 118140960795 + 5723036 * 2 ^ 59
def prefixEnd_5723036 : Nat := 4983230072969 + 3 ^ 40 * 5723036 * 2
def baseEnd_5723036 : Nat := 2938668270984775829030243

theorem tailTrace_5723036 : CollatzResearch.WordTrace tailWord_5723036 prefixEnd_5723036 2938668270984775829030243 := by
  unfold tailWord_5723036
  simp only [CollatzResearch.WordTrace]
  refine ⟨104368135647212731788894481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139157514196283642385192641 104368135647212731788894481)
  ·
    refine ⟨78276101735409548841670861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104368135647212731788894481 78276101735409548841670861)
    ·
      refine ⟨29353538150778580815626573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78276101735409548841670861 29353538150778580815626573)
      ·
        refine ⟨11007576806541967805859965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29353538150778580815626573 11007576806541967805859965)
        ·
          refine ⟨4127841302453237927197487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11007576806541967805859965 4127841302453237927197487)
          ·
            refine ⟨6191761953679856890796231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127841302453237927197487 6191761953679856890796231)
            ·
              refine ⟨9287642930519785336194347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191761953679856890796231 9287642930519785336194347)
              ·
                refine ⟨13931464395779678004291521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287642930519785336194347 13931464395779678004291521)
                ·
                  refine ⟨10448598296834758503218641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13931464395779678004291521 10448598296834758503218641)
                  ·
                    refine ⟨7836448722626068877413981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10448598296834758503218641 7836448722626068877413981)
                    ·
                      refine ⟨2938668270984775829030243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836448722626068877413981 2938668270984775829030243)
                      ·
                        rfl

theorem cell23_5723036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5723036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723036 prefixEnd_5723036 := by exact prefixLift 5723036
  have htrace : WordTrace (prefixWord ++ tailWord_5723036) baseStart_5723036 baseEnd_5723036 := by
    simpa [prefixWord, tailWord_5723036, baseEnd_5723036] using wordTrace_append hprefix tailTrace_5723036
  have hstable : (prefixWord ++ tailWord_5723036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723036).length < 2 ^ (prefixWord ++ tailWord_5723036).sum := by decide
  have hdescent : baseEnd_5723036 < baseStart_5723036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723049 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 1, 1, 3]
def baseStart_5723049 : Nat := 118140960795 + 5723049 * 2 ^ 59
def prefixEnd_5723049 : Nat := 4983230072969 + 3 ^ 40 * 5723049 * 2
def baseEnd_5723049 : Nat := 2938674946233284278167683

theorem tailTrace_5723049 : CollatzResearch.WordTrace tailWord_5723049 prefixEnd_5723049 2938674946233284278167683 := by
  unfold tailWord_5723049
  simp only [CollatzResearch.WordTrace]
  refine ⟨208736745443378366798012201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139157830295585577865341467 208736745443378366798012201)
  ·
    refine ⟨156552559082533775098509151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208736745443378366798012201 156552559082533775098509151)
    ·
      refine ⟨234828838623800662647763727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156552559082533775098509151 234828838623800662647763727)
      ·
        refine ⟨352243257935700993971645591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234828838623800662647763727 352243257935700993971645591)
        ·
          refine ⟨528364886903551490957468387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352243257935700993971645591 528364886903551490957468387)
          ·
            refine ⟨792547330355327236436202581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528364886903551490957468387 792547330355327236436202581)
            ·
              refine ⟨9287664027601491051986749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 792547330355327236436202581 9287664027601491051986749)
              ·
                refine ⟨3482874010350559144495031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9287664027601491051986749 3482874010350559144495031)
                ·
                  refine ⟨5224311015525838716742547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482874010350559144495031 5224311015525838716742547)
                  ·
                    refine ⟨7836466523288758075113821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5224311015525838716742547 7836466523288758075113821)
                    ·
                      refine ⟨2938674946233284278167683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836466523288758075113821 2938674946233284278167683)
                      ·
                        rfl

theorem cell23_5723049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 1, 3].length) (baseStart_5723049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723049 prefixEnd_5723049 := by exact prefixLift 5723049
  have htrace : WordTrace (prefixWord ++ tailWord_5723049) baseStart_5723049 baseEnd_5723049 := by
    simpa [prefixWord, tailWord_5723049, baseEnd_5723049] using wordTrace_append hprefix tailTrace_5723049
  have hstable : (prefixWord ++ tailWord_5723049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723049).length < 2 ^ (prefixWord ++ tailWord_5723049).sum := by decide
  have hdescent : baseEnd_5723049 < baseStart_5723049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723105 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_5723105 : Nat := 118140960795 + 5723105 * 2 ^ 59
def prefixEnd_5723105 : Nat := 4983230072969 + 3 ^ 40 * 5723105 * 2
def baseEnd_5723105 : Nat := 2938703701149936059067425

theorem tailTrace_5723105 : CollatzResearch.WordTrace tailWord_5723105 prefixEnd_5723105 2938703701149936059067425 := by
  unfold tailWord_5723105
  simp only [CollatzResearch.WordTrace]
  refine ⟨208738787931175488362050769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139159191954116992241367179 208738787931175488362050769)
  ·
    refine ⟨156554090948381616271538077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208738787931175488362050769 156554090948381616271538077)
    ·
      refine ⟨58707784105643106101826779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156554090948381616271538077 58707784105643106101826779)
      ·
        refine ⟨88061676158464659152740169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58707784105643106101826779 88061676158464659152740169)
        ·
          refine ⟨66046257118848494364555127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88061676158464659152740169 66046257118848494364555127)
          ·
            refine ⟨99069385678272741546832691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66046257118848494364555127 99069385678272741546832691)
            ·
              refine ⟨148604078517409112320249037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99069385678272741546832691 148604078517409112320249037)
              ·
                refine ⟨55726529444028417120093389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148604078517409112320249037 55726529444028417120093389)
                ·
                  refine ⟨20897448541510656420035021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55726529444028417120093389 20897448541510656420035021)
                  ·
                    refine ⟨7836543203066496157513133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20897448541510656420035021 7836543203066496157513133)
                    ·
                      refine ⟨2938703701149936059067425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836543203066496157513133 2938703701149936059067425)
                      ·
                        rfl

theorem cell23_5723105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_5723105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723105 prefixEnd_5723105 := by exact prefixLift 5723105
  have htrace : WordTrace (prefixWord ++ tailWord_5723105) baseStart_5723105 baseEnd_5723105 := by
    simpa [prefixWord, tailWord_5723105, baseEnd_5723105] using wordTrace_append hprefix tailTrace_5723105
  have hstable : (prefixWord ++ tailWord_5723105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723105).length < 2 ^ (prefixWord ++ tailWord_5723105).sum := by decide
  have hdescent : baseEnd_5723105 < baseStart_5723105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723109 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5723109 : Nat := 118140960795 + 5723109 * 2 ^ 59
def prefixEnd_5723109 : Nat := 4983230072969 + 3 ^ 40 * 5723109 * 2
def baseEnd_5723109 : Nat := 2938705755072554043417407

theorem tailTrace_5723109 : CollatzResearch.WordTrace tailWord_5723109 prefixEnd_5723109 2938705755072554043417407 := by
  unfold tailWord_5723109
  simp only [CollatzResearch.WordTrace]
  refine ⟨208738933823160997045196381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139159289215440664696797587 208738933823160997045196381)
  ·
    refine ⟨78277100183685373891948643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208738933823160997045196381 78277100183685373891948643)
    ·
      refine ⟨117415650275528060837922965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78277100183685373891948643 117415650275528060837922965)
      ·
        refine ⟨5503858606665377851777639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117415650275528060837922965 5503858606665377851777639)
        ·
          refine ⟨8255787909998066777666459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503858606665377851777639 8255787909998066777666459)
          ·
            refine ⟨12383681864997100166499689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8255787909998066777666459 12383681864997100166499689)
            ·
              refine ⟨9287761398747825124874767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12383681864997100166499689 9287761398747825124874767)
              ·
                refine ⟨13931642098121737687312151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287761398747825124874767 13931642098121737687312151)
                ·
                  refine ⟨20897463147182606530968227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13931642098121737687312151 20897463147182606530968227)
                  ·
                    refine ⟨31346194720773909796452341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20897463147182606530968227 31346194720773909796452341)
                    ·
                      refine ⟨2938705755072554043417407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31346194720773909796452341 2938705755072554043417407)
                      ·
                        rfl

theorem cell23_5723109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5723109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723109 prefixEnd_5723109 := by exact prefixLift 5723109
  have htrace : WordTrace (prefixWord ++ tailWord_5723109) baseStart_5723109 baseEnd_5723109 := by
    simpa [prefixWord, tailWord_5723109, baseEnd_5723109] using wordTrace_append hprefix tailTrace_5723109
  have hstable : (prefixWord ++ tailWord_5723109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723109).length < 2 ^ (prefixWord ++ tailWord_5723109).sum := by decide
  have hdescent : baseEnd_5723109 < baseStart_5723109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723182 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_5723182 : Nat := 118140960795 + 5723182 * 2 ^ 59
def prefixEnd_5723182 : Nat := 4983230072969 + 3 ^ 40 * 5723182 * 2
def baseEnd_5723182 : Nat := 2938743239160332257804571

theorem tailTrace_5723182 : CollatzResearch.WordTrace tailWord_5723182 prefixEnd_5723182 2938743239160332257804571 := by
  unfold tailWord_5723182
  simp only [CollatzResearch.WordTrace]
  refine ⟨26092699543987066314075475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139161064234597687008402533 26092699543987066314075475)
  ·
    refine ⟨39139049315980599471113213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26092699543987066314075475 39139049315980599471113213)
    ·
      refine ⟨14677143493492724801667455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39139049315980599471113213 14677143493492724801667455)
      ·
        refine ⟨22015715240239087202501183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14677143493492724801667455 22015715240239087202501183)
        ·
          refine ⟨33023572860358630803751775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22015715240239087202501183 33023572860358630803751775)
          ·
            refine ⟨49535359290537946205627663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33023572860358630803751775 49535359290537946205627663)
            ·
              refine ⟨74303038935806919308441495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49535359290537946205627663 74303038935806919308441495)
              ·
                refine ⟨111454558403710378962662243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74303038935806919308441495 111454558403710378962662243)
                ·
                  refine ⟨167181837605565568443993365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111454558403710378962662243 167181837605565568443993365)
                  ·
                    refine ⟨7836648637760886020812189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 167181837605565568443993365 7836648637760886020812189)
                    ·
                      refine ⟨2938743239160332257804571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836648637760886020812189 2938743239160332257804571)
                      ·
                        rfl

theorem cell23_5723182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_5723182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723182 prefixEnd_5723182 := by exact prefixLift 5723182
  have htrace : WordTrace (prefixWord ++ tailWord_5723182) baseStart_5723182 baseEnd_5723182 := by
    simpa [prefixWord, tailWord_5723182, baseEnd_5723182] using wordTrace_append hprefix tailTrace_5723182
  have hstable : (prefixWord ++ tailWord_5723182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723182).length < 2 ^ (prefixWord ++ tailWord_5723182).sum := by decide
  have hdescent : baseEnd_5723182 < baseStart_5723182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723185 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 7]
def baseStart_5723185 : Nat := 118140960795 + 5723185 * 2 ^ 59
def prefixEnd_5723185 : Nat := 4983230072969 + 3 ^ 40 * 5723185 * 2
def baseEnd_5723185 : Nat := 326527197733588416229673

theorem tailTrace_5723185 : CollatzResearch.WordTrace tailWord_5723185 prefixEnd_5723185 326527197733588416229673 := by
  unfold tailWord_5723185
  simp only [CollatzResearch.WordTrace]
  refine ⟨208741705770885662024963009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139161137180590441349975339 208741705770885662024963009)
  ·
    refine ⟨156556279328164246518722257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208741705770885662024963009 156556279328164246518722257)
    ·
      refine ⟨117417209496123184889041693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156556279328164246518722257 117417209496123184889041693)
      ·
        refine ⟨44031453561046194333390635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117417209496123184889041693 44031453561046194333390635)
        ·
          refine ⟨66047180341569291500085953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44031453561046194333390635 66047180341569291500085953)
          ·
            refine ⟨49535385256176968625064465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66047180341569291500085953 49535385256176968625064465)
            ·
              refine ⟨37151538942132726468798349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49535385256176968625064465 37151538942132726468798349)
              ·
                refine ⟨13931827103299772425799381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37151538942132726468798349 13931827103299772425799381)
                ·
                  refine ⟨326527197733588416229673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13931827103299772425799381 326527197733588416229673)
                  ·
                    rfl

theorem cell23_5723185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_5723185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723185 prefixEnd_5723185 := by exact prefixLift 5723185
  have htrace : WordTrace (prefixWord ++ tailWord_5723185) baseStart_5723185 baseEnd_5723185 := by
    simpa [prefixWord, tailWord_5723185, baseEnd_5723185] using wordTrace_append hprefix tailTrace_5723185
  have hstable : (prefixWord ++ tailWord_5723185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723185).length < 2 ^ (prefixWord ++ tailWord_5723185).sum := by decide
  have hdescent : baseEnd_5723185 < baseStart_5723185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723192 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_5723192 : Nat := 118140960795 + 5723192 * 2 ^ 59
def prefixEnd_5723192 : Nat := 4983230072969 + 3 ^ 40 * 5723192 * 2
def baseEnd_5723192 : Nat := 2938748373966877218679525

theorem tailTrace_5723192 : CollatzResearch.WordTrace tailWord_5723192 prefixEnd_5723192 2938748373966877218679525 := by
  unfold tailWord_5723192
  simp only [CollatzResearch.WordTrace]
  refine ⟨104370980540930151110233915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139161307387906868146978553 104370980540930151110233915)
  ·
    refine ⟨156556470811395226665350873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104370980540930151110233915 156556470811395226665350873)
    ·
      refine ⟨117417353108546419999013155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156556470811395226665350873 117417353108546419999013155)
      ·
        refine ⟨176126029662819629998519733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117417353108546419999013155 176126029662819629998519733)
        ·
          refine ⟨16511815280889340312361225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176126029662819629998519733 16511815280889340312361225)
          ·
            refine ⟨12383861460667005234270919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16511815280889340312361225 12383861460667005234270919)
            ·
              refine ⟨18575792191000507851406379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12383861460667005234270919 18575792191000507851406379)
              ·
                refine ⟨27863688286500761777109569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18575792191000507851406379 27863688286500761777109569)
                ·
                  refine ⟨20897766214875571332832177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27863688286500761777109569 20897766214875571332832177)
                  ·
                    refine ⟨15673324661156678499624133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20897766214875571332832177 15673324661156678499624133)
                    ·
                      refine ⟨2938748373966877218679525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15673324661156678499624133 2938748373966877218679525)
                      ·
                        rfl

theorem cell23_5723192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_5723192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723192 prefixEnd_5723192 := by exact prefixLift 5723192
  have htrace : WordTrace (prefixWord ++ tailWord_5723192) baseStart_5723192 baseEnd_5723192 := by
    simpa [prefixWord, tailWord_5723192, baseEnd_5723192] using wordTrace_append hprefix tailTrace_5723192
  have hstable : (prefixWord ++ tailWord_5723192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723192).length < 2 ^ (prefixWord ++ tailWord_5723192).sum := by decide
  have hdescent : baseEnd_5723192 < baseStart_5723192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723196 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_5723196 : Nat := 118140960795 + 5723196 * 2 ^ 59
def prefixEnd_5723196 : Nat := 4983230072969 + 3 ^ 40 * 5723196 * 2
def baseEnd_5723196 : Nat := 2938750427889495203029507

theorem tailTrace_5723196 : CollatzResearch.WordTrace tailWord_5723196 prefixEnd_5723196 2938750427889495203029507 := by
  unfold tailWord_5723196
  simp only [CollatzResearch.WordTrace]
  refine ⟨104371053486922905451806721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139161404649230540602408961 104371053486922905451806721)
  ·
    refine ⟨78278290115192179088855041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104371053486922905451806721 78278290115192179088855041)
    ·
      refine ⟨58708717586394134316641281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78278290115192179088855041 58708717586394134316641281)
      ·
        refine ⟨44031538189795600737480961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58708717586394134316641281 44031538189795600737480961)
        ·
          refine ⟨33023653642346700553110721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44031538189795600737480961 33023653642346700553110721)
          ·
            refine ⟨24767740231760025414833041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33023653642346700553110721 24767740231760025414833041)
            ·
              refine ⟨18575805173820019061124781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24767740231760025414833041 18575805173820019061124781)
              ·
                refine ⟨6965926940182507147921793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18575805173820019061124781 6965926940182507147921793)
                ·
                  refine ⟨5224445205136880360941345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6965926940182507147921793 5224445205136880360941345)
                  ·
                    refine ⟨3918333903852660270706009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5224445205136880360941345 3918333903852660270706009)
                    ·
                      refine ⟨2938750427889495203029507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918333903852660270706009 2938750427889495203029507)
                      ·
                        rfl

theorem cell23_5723196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_5723196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723196 prefixEnd_5723196 := by exact prefixLift 5723196
  have htrace : WordTrace (prefixWord ++ tailWord_5723196) baseStart_5723196 baseEnd_5723196 := by
    simpa [prefixWord, tailWord_5723196, baseEnd_5723196] using wordTrace_append hprefix tailTrace_5723196
  have hstable : (prefixWord ++ tailWord_5723196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723196).length < 2 ^ (prefixWord ++ tailWord_5723196).sum := by decide
  have hdescent : baseEnd_5723196 < baseStart_5723196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723225 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_5723225 : Nat := 118140960795 + 5723225 * 2 ^ 59
def prefixEnd_5723225 : Nat := 4983230072969 + 3 ^ 40 * 5723225 * 2
def baseEnd_5723225 : Nat := 2938765318828475589566873

theorem tailTrace_5723225 : CollatzResearch.WordTrace tailWord_5723225 prefixEnd_5723225 2938765318828475589566873 := by
  unfold tailWord_5723225
  simp only [CollatzResearch.WordTrace]
  refine ⟨208743164690740748856419129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139162109793827165904279419 208743164690740748856419129)
  ·
    refine ⟨156557373518055561642314347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208743164690740748856419129 156557373518055561642314347)
    ·
      refine ⟨234836060277083342463471521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156557373518055561642314347 234836060277083342463471521)
      ·
        refine ⟨176127045207812506847603641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234836060277083342463471521 176127045207812506847603641)
        ·
          refine ⟨132095283905859380135702731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176127045207812506847603641 132095283905859380135702731)
          ·
            refine ⟨198142925858789070203554097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132095283905859380135702731 198142925858789070203554097)
            ·
              refine ⟨148607194394091802652665573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198142925858789070203554097 148607194394091802652665573)
              ·
                refine ⟨27863848948892212997374795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148607194394091802652665573 27863848948892212997374795)
                ·
                  refine ⟨41795773423338319496062193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27863848948892212997374795 41795773423338319496062193)
                  ·
                    refine ⟨31346830067503739622046645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41795773423338319496062193 31346830067503739622046645)
                    ·
                      refine ⟨2938765318828475589566873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31346830067503739622046645 2938765318828475589566873)
                      ·
                        rfl

theorem cell23_5723225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_5723225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723225 prefixEnd_5723225 := by exact prefixLift 5723225
  have htrace : WordTrace (prefixWord ++ tailWord_5723225) baseStart_5723225 baseEnd_5723225 := by
    simpa [prefixWord, tailWord_5723225, baseEnd_5723225] using wordTrace_append hprefix tailTrace_5723225
  have hstable : (prefixWord ++ tailWord_5723225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723225).length < 2 ^ (prefixWord ++ tailWord_5723225).sum := by decide
  have hdescent : baseEnd_5723225 < baseStart_5723225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723230 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5723230 : Nat := 118140960795 + 5723230 * 2 ^ 59
def prefixEnd_5723230 : Nat := 4983230072969 + 3 ^ 40 * 5723230 * 2
def baseEnd_5723230 : Nat := 2938767886231748070004351

theorem tailTrace_5723230 : CollatzResearch.WordTrace tailWord_5723230 prefixEnd_5723230 2938767886231748070004351 := by
  unfold tailWord_5723230
  simp only [CollatzResearch.WordTrace]
  refine ⟨26092918381965329338793893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139162231370481756473567429 26092918381965329338793893)
  ·
    refine ⟨4892422196618499251023855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26092918381965329338793893 4892422196618499251023855)
    ·
      refine ⟨7338633294927748876535783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4892422196618499251023855 7338633294927748876535783)
      ·
        refine ⟨11007949942391623314803675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7338633294927748876535783 11007949942391623314803675)
        ·
          refine ⟨16511924913587434972205513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11007949942391623314803675 16511924913587434972205513)
          ·
            refine ⟨12383943685190576229154135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16511924913587434972205513 12383943685190576229154135)
            ·
              refine ⟨18575915527785864343731203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12383943685190576229154135 18575915527785864343731203)
              ·
                refine ⟨27863873291678796515596805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18575915527785864343731203 27863873291678796515596805)
                ·
                  refine ⟨5224476242189774346674401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27863873291678796515596805 5224476242189774346674401)
                  ·
                    refine ⟨3918357181642330760005801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5224476242189774346674401 3918357181642330760005801)
                    ·
                      refine ⟨2938767886231748070004351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918357181642330760005801 2938767886231748070004351)
                      ·
                        rfl

theorem cell23_5723230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5723230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723230 prefixEnd_5723230 := by exact prefixLift 5723230
  have htrace : WordTrace (prefixWord ++ tailWord_5723230) baseStart_5723230 baseEnd_5723230 := by
    simpa [prefixWord, tailWord_5723230, baseEnd_5723230] using wordTrace_append hprefix tailTrace_5723230
  have hstable : (prefixWord ++ tailWord_5723230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723230).length < 2 ^ (prefixWord ++ tailWord_5723230).sum := by decide
  have hdescent : baseEnd_5723230 < baseStart_5723230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723292 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 8]
def baseStart_5723292 : Nat := 118140960795 + 5723292 * 2 ^ 59
def prefixEnd_5723292 : Nat := 4983230072969 + 3 ^ 40 * 5723292 * 2
def baseEnd_5723292 : Nat := 326533302448036314158785

theorem tailTrace_5723292 : CollatzResearch.WordTrace tailWord_5723292 prefixEnd_5723292 326533302448036314158785 := by
  unfold tailWord_5723292
  simp only [CollatzResearch.WordTrace]
  refine ⟨104372804190749009649554065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139163738920998679532738753 104372804190749009649554065)
  ·
    refine ⟨78279603143061757237165549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104372804190749009649554065 78279603143061757237165549)
    ·
      refine ⟨29354851178648158963937081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78279603143061757237165549 29354851178648158963937081)
      ·
        refine ⟨22016138383986119222952811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29354851178648158963937081 22016138383986119222952811)
        ·
          refine ⟨33024207575979178834429217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22016138383986119222952811 33024207575979178834429217)
          ·
            refine ⟨24768155681984384125821913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33024207575979178834429217 24768155681984384125821913)
            ·
              refine ⟨18576116761488288094366435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24768155681984384125821913 18576116761488288094366435)
              ·
                refine ⟨27864175142232432141549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18576116761488288094366435 27864175142232432141549653)
                ·
                  refine ⟨326533302448036314158785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27864175142232432141549653 326533302448036314158785)
                  ·
                    rfl

theorem cell23_5723292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_5723292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723292 prefixEnd_5723292 := by exact prefixLift 5723292
  have htrace : WordTrace (prefixWord ++ tailWord_5723292) baseStart_5723292 baseEnd_5723292 := by
    simpa [prefixWord, tailWord_5723292, baseEnd_5723292] using wordTrace_append hprefix tailTrace_5723292
  have hstable : (prefixWord ++ tailWord_5723292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723292).length < 2 ^ (prefixWord ++ tailWord_5723292).sum := by decide
  have hdescent : baseEnd_5723292 < baseStart_5723292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723319 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_5723319 : Nat := 118140960795 + 5723319 * 2 ^ 59
def prefixEnd_5723319 : Nat := 4983230072969 + 3 ^ 40 * 5723319 * 2
def baseEnd_5723319 : Nat := 2938813586009998221791441

theorem tailTrace_5723319 : CollatzResearch.WordTrace tailWord_5723319 prefixEnd_5723319 2938813586009998221791441 := by
  unfold tailWord_5723319
  simp only [CollatzResearch.WordTrace]
  refine ⟨208746593152400202910341011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139164395434933468606894007 208746593152400202910341011)
  ·
    refine ⟨313119889728600304365511517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208746593152400202910341011 313119889728600304365511517)
    ·
      refine ⟨117419958648225114137066819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313119889728600304365511517 117419958648225114137066819)
      ·
        refine ⟨176129937972337671205600229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117419958648225114137066819 176129937972337671205600229)
        ·
          refine ⟨33024363369813313351050043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176129937972337671205600229 33024363369813313351050043)
          ·
            refine ⟨49536545054719970026575065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33024363369813313351050043 49536545054719970026575065)
            ·
              refine ⟨37152408791039977519931299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49536545054719970026575065 37152408791039977519931299)
              ·
                refine ⟨55728613186559966279896949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37152408791039977519931299 55728613186559966279896949)
                ·
                  refine ⟨5224557486239996838740339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55728613186559966279896949 5224557486239996838740339)
                  ·
                    refine ⟨7836836229359995258110509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5224557486239996838740339 7836836229359995258110509)
                    ·
                      refine ⟨2938813586009998221791441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836836229359995258110509 2938813586009998221791441)
                      ·
                        rfl

theorem cell23_5723319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_5723319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723319 prefixEnd_5723319 := by exact prefixLift 5723319
  have htrace : WordTrace (prefixWord ++ tailWord_5723319) baseStart_5723319 baseEnd_5723319 := by
    simpa [prefixWord, tailWord_5723319, baseEnd_5723319] using wordTrace_append hprefix tailTrace_5723319
  have hstable : (prefixWord ++ tailWord_5723319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723319).length < 2 ^ (prefixWord ++ tailWord_5723319).sum := by decide
  have hdescent : baseEnd_5723319 < baseStart_5723319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723346 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_5723346 : Nat := 118140960795 + 5723346 * 2 ^ 59
def prefixEnd_5723346 : Nat := 4983230072969 + 3 ^ 40 * 5723346 * 2
def baseEnd_5723346 : Nat := 2938827449987669616153817

theorem tailTrace_5723346 : CollatzResearch.WordTrace tailWord_5723346 prefixEnd_5723346 2938827449987669616153817 := by
  unfold tailWord_5723346
  simp only [CollatzResearch.WordTrace]
  refine ⟨52186894480825596630393473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139165051948868257681049261 52186894480825596630393473)
  ·
    refine ⟨39140170860619197472795105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52186894480825596630393473 39140170860619197472795105)
    ·
      refine ⟨29355128145464398104596329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39140170860619197472795105 29355128145464398104596329)
      ·
        refine ⟨22016346109098298578447247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29355128145464398104596329 22016346109098298578447247)
        ·
          refine ⟨33024519163647447867670871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22016346109098298578447247 33024519163647447867670871)
          ·
            refine ⟨49536778745471171801506307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33024519163647447867670871 49536778745471171801506307)
            ·
              refine ⟨74305168118206757702259461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49536778745471171801506307 74305168118206757702259461)
              ·
                refine ⟨13932219022163767069173649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74305168118206757702259461 13932219022163767069173649)
                ·
                  refine ⟨10449164266622825301880237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13932219022163767069173649 10449164266622825301880237)
                  ·
                    refine ⟨3918436599983559488205089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10449164266622825301880237 3918436599983559488205089)
                    ·
                      refine ⟨2938827449987669616153817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918436599983559488205089 2938827449987669616153817)
                      ·
                        rfl

theorem cell23_5723346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_5723346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723346 prefixEnd_5723346 := by exact prefixLift 5723346
  have htrace : WordTrace (prefixWord ++ tailWord_5723346) baseStart_5723346 baseEnd_5723346 := by
    simpa [prefixWord, tailWord_5723346, baseEnd_5723346] using wordTrace_append hprefix tailTrace_5723346
  have hstable : (prefixWord ++ tailWord_5723346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723346).length < 2 ^ (prefixWord ++ tailWord_5723346).sum := by decide
  have hdescent : baseEnd_5723346 < baseStart_5723346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723379 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 3]
def baseStart_5723379 : Nat := 118140960795 + 5723379 * 2 ^ 59
def prefixEnd_5723379 : Nat := 4983230072969 + 3 ^ 40 * 5723379 * 2
def baseEnd_5723379 : Nat := 2938844394849267987041165

theorem tailTrace_5723379 : CollatzResearch.WordTrace tailWord_5723379 prefixEnd_5723379 2938844394849267987041165 := by
  unfold tailWord_5723379
  simp only [CollatzResearch.WordTrace]
  refine ⟨208748781532182833157525191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139165854354788555438350127 208748781532182833157525191)
  ·
    refine ⟨313123172298274249736287787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208748781532182833157525191 313123172298274249736287787)
    ·
      refine ⟨469684758447411374604431681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313123172298274249736287787 469684758447411374604431681)
      ·
        refine ⟨352263568835558530953323761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469684758447411374604431681 352263568835558530953323761)
        ·
          refine ⟨264197676626668898214992821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352263568835558530953323761 264197676626668898214992821)
          ·
            refine ⟨24768532183750209207655577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264197676626668898214992821 24768532183750209207655577)
            ·
              refine ⟨18576399137812656905741683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24768532183750209207655577 18576399137812656905741683)
              ·
                refine ⟨27864598706718985358612525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18576399137812656905741683 27864598706718985358612525)
                ·
                  refine ⟨10449224515019619509479697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27864598706718985358612525 10449224515019619509479697)
                  ·
                    refine ⟨7836918386264714632109773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10449224515019619509479697 7836918386264714632109773)
                    ·
                      refine ⟨2938844394849267987041165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7836918386264714632109773 2938844394849267987041165)
                      ·
                        rfl

theorem cell23_5723379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_5723379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723379 prefixEnd_5723379 := by exact prefixLift 5723379
  have htrace : WordTrace (prefixWord ++ tailWord_5723379) baseStart_5723379 baseEnd_5723379 := by
    simpa [prefixWord, tailWord_5723379, baseEnd_5723379] using wordTrace_append hprefix tailTrace_5723379
  have hstable : (prefixWord ++ tailWord_5723379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723379).length < 2 ^ (prefixWord ++ tailWord_5723379).sum := by decide
  have hdescent : baseEnd_5723379 < baseStart_5723379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723393 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_5723393 : Nat := 118140960795 + 5723393 * 2 ^ 59
def prefixEnd_5723393 : Nat := 4983230072969 + 3 ^ 40 * 5723393 * 2
def baseEnd_5723393 : Nat := 2938851583578430932266101

theorem tailTrace_5723393 : CollatzResearch.WordTrace tailWord_5723393 prefixEnd_5723393 2938851583578430932266101 := by
  unfold tailWord_5723393
  simp only [CollatzResearch.WordTrace]
  refine ⟨208749292154132113548534833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139166194769421409032356555 208749292154132113548534833)
  ·
    refine ⟨156561969115599085161401125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208749292154132113548534833 156561969115599085161401125)
    ·
      refine ⟨29355369209174828467762711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156561969115599085161401125 29355369209174828467762711)
      ·
        refine ⟨44033053813762242701644067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29355369209174828467762711 44033053813762242701644067)
        ·
          refine ⟨66049580720643364052466101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44033053813762242701644067 66049580720643364052466101)
          ·
            refine ⟨6192148192560315379918697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66049580720643364052466101 6192148192560315379918697)
            ·
              refine ⟨4644111144420236534939023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6192148192560315379918697 4644111144420236534939023)
              ·
                refine ⟨6966166716630354802408535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644111144420236534939023 6966166716630354802408535)
                ·
                  refine ⟨10449250074945532203612803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6966166716630354802408535 10449250074945532203612803)
                  ·
                    refine ⟨15673875112418298305419205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10449250074945532203612803 15673875112418298305419205)
                    ·
                      refine ⟨2938851583578430932266101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15673875112418298305419205 2938851583578430932266101)
                      ·
                        rfl

theorem cell23_5723393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_5723393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723393 prefixEnd_5723393 := by exact prefixLift 5723393
  have htrace : WordTrace (prefixWord ++ tailWord_5723393) baseStart_5723393 baseEnd_5723393 := by
    simpa [prefixWord, tailWord_5723393, baseEnd_5723393] using wordTrace_append hprefix tailTrace_5723393
  have hstable : (prefixWord ++ tailWord_5723393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723393).length < 2 ^ (prefixWord ++ tailWord_5723393).sum := by decide
  have hdescent : baseEnd_5723393 < baseStart_5723393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723402 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5723402 : Nat := 118140960795 + 5723402 * 2 ^ 59
def prefixEnd_5723402 : Nat := 4983230072969 + 3 ^ 40 * 5723402 * 2
def baseEnd_5723402 : Nat := 2938856204904321397053559

theorem tailTrace_5723402 : CollatzResearch.WordTrace tailWord_5723402 prefixEnd_5723402 2938856204904321397053559 := by
  unfold tailWord_5723402
  simp only [CollatzResearch.WordTrace]
  refine ⟨52187405102774877021403115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139166413607399672057074973 52187405102774877021403115)
  ·
    refine ⟨78281107654162315532104673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52187405102774877021403115 78281107654162315532104673)
    ·
      refine ⟨58710830740621736649078505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78281107654162315532104673 58710830740621736649078505)
      ·
        refine ⟨44033123055466302486808879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58710830740621736649078505 44033123055466302486808879)
        ·
          refine ⟨66049684583199453730213319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44033123055466302486808879 66049684583199453730213319)
          ·
            refine ⟨99074526874799180595319979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66049684583199453730213319 99074526874799180595319979)
            ·
              refine ⟨148611790312198770892979969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99074526874799180595319979 148611790312198770892979969)
              ·
                refine ⟨111458842734149078169734977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148611790312198770892979969 111458842734149078169734977)
                ·
                  refine ⟨83594132050611808627301233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111458842734149078169734977 83594132050611808627301233)
                  ·
                    refine ⟨62695599037958856470475925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83594132050611808627301233 62695599037958856470475925)
                    ·
                      refine ⟨2938856204904321397053559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62695599037958856470475925 2938856204904321397053559)
                      ·
                        rfl

theorem cell23_5723402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5723402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723402 prefixEnd_5723402 := by exact prefixLift 5723402
  have htrace : WordTrace (prefixWord ++ tailWord_5723402) baseStart_5723402 baseEnd_5723402 := by
    simpa [prefixWord, tailWord_5723402, baseEnd_5723402] using wordTrace_append hprefix tailTrace_5723402
  have hstable : (prefixWord ++ tailWord_5723402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723402).length < 2 ^ (prefixWord ++ tailWord_5723402).sum := by decide
  have hdescent : baseEnd_5723402 < baseStart_5723402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723423 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 1, 2, 4]
def baseStart_5723423 : Nat := 118140960795 + 5723423 * 2 ^ 59
def prefixEnd_5723423 : Nat := 4983230072969 + 3 ^ 40 * 5723423 * 2
def baseEnd_5723423 : Nat := 2938866987998065814890963

theorem tailTrace_5723423 : CollatzResearch.WordTrace tailWord_5723423 prefixEnd_5723423 2938866987998065814890963 := by
  unfold tailWord_5723423
  simp only [CollatzResearch.WordTrace]
  refine ⟨208750386344023428672126923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139166924229348952448084615 208750386344023428672126923)
  ·
    refine ⟨313125579516035143008190385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208750386344023428672126923 313125579516035143008190385)
    ·
      refine ⟨234844184637026357256142789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313125579516035143008190385 234844184637026357256142789)
      ·
        refine ⟨44033284619442441985526773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234844184637026357256142789 44033284619442441985526773)
        ·
          refine ⟨4128120433072728936143135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44033284619442441985526773 4128120433072728936143135)
          ·
            refine ⟨6192180649609093404214703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128120433072728936143135 6192180649609093404214703)
            ·
              refine ⟨9288270974413640106322055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192180649609093404214703 9288270974413640106322055)
              ·
                refine ⟨13932406461620460159483083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288270974413640106322055 13932406461620460159483083)
                ·
                  refine ⟨20898609692430690239224625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13932406461620460159483083 20898609692430690239224625)
                  ·
                    refine ⟨15673957269323017679418469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20898609692430690239224625 15673957269323017679418469)
                    ·
                      refine ⟨2938866987998065814890963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15673957269323017679418469 2938866987998065814890963)
                      ·
                        rfl

theorem cell23_5723423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_5723423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723423 prefixEnd_5723423 := by exact prefixLift 5723423
  have htrace : WordTrace (prefixWord ++ tailWord_5723423) baseStart_5723423 baseEnd_5723423 := by
    simpa [prefixWord, tailWord_5723423, baseEnd_5723423] using wordTrace_append hprefix tailTrace_5723423
  have hstable : (prefixWord ++ tailWord_5723423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723423).length < 2 ^ (prefixWord ++ tailWord_5723423).sum := by decide
  have hdescent : baseEnd_5723423 < baseStart_5723423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723506 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_5723506 : Nat := 118140960795 + 5723506 * 2 ^ 59
def prefixEnd_5723506 : Nat := 4983230072969 + 3 ^ 40 * 5723506 * 2
def baseEnd_5723506 : Nat := 326545511876932110017009

theorem tailTrace_5723506 : CollatzResearch.WordTrace tailWord_5723506 prefixEnd_5723506 326545511876932110017009 := by
  unfold tailWord_5723506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52188353400680683461849593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139168942401815155898265581 52188353400680683461849593)
  ·
    refine ⟨39141265050510512596387195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52188353400680683461849593 39141265050510512596387195)
    ·
      refine ⟨58711897575765768894580793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39141265050510512596387195 58711897575765768894580793)
      ·
        refine ⟨44033923181824326670935595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58711897575765768894580793 44033923181824326670935595)
        ·
          refine ⟨66050884772736490006403393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44033923181824326670935595 66050884772736490006403393)
          ·
            refine ⟨49538163579552367504802545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66050884772736490006403393 49538163579552367504802545)
            ·
              refine ⟨37153622684664275628601909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49538163579552367504802545 37153622684664275628601909)
              ·
                refine ⟨3483152126687275840181429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37153622684664275628601909 3483152126687275840181429)
                ·
                  refine ⟨326545511876932110017009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3483152126687275840181429 326545511876932110017009)
                  ·
                    rfl

theorem cell23_5723506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_5723506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723506 prefixEnd_5723506 := by exact prefixLift 5723506
  have htrace : WordTrace (prefixWord ++ tailWord_5723506) baseStart_5723506 baseEnd_5723506 := by
    simpa [prefixWord, tailWord_5723506, baseEnd_5723506] using wordTrace_append hprefix tailTrace_5723506
  have hstable : (prefixWord ++ tailWord_5723506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723506).length < 2 ^ (prefixWord ++ tailWord_5723506).sum := by decide
  have hdescent : baseEnd_5723506 < baseStart_5723506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723523 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 5]
def baseStart_5723523 : Nat := 118140960795 + 5723523 * 2 ^ 59
def prefixEnd_5723523 : Nat := 4983230072969 + 3 ^ 40 * 5723523 * 2
def baseEnd_5723523 : Nat := 326546481784835047071167

theorem tailTrace_5723523 : CollatzResearch.WordTrace tailWord_5723523 prefixEnd_5723523 326546481784835047071167 := by
  unfold tailWord_5723523
  simp only [CollatzResearch.WordTrace]
  refine ⟨208754033643661145750767223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139169355762440763833844815 208754033643661145750767223)
  ·
    refine ⟨313131050465491718626150835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208754033643661145750767223 313131050465491718626150835)
    ·
      refine ⟨469696575698237577939226253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313131050465491718626150835 469696575698237577939226253)
      ·
        refine ⟨176136215886839091727209845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469696575698237577939226253 176136215886839091727209845)
        ·
          refine ⟨16512770239391164849425923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176136215886839091727209845 16512770239391164849425923)
          ·
            refine ⟨24769155359086747274138885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16512770239391164849425923 24769155359086747274138885)
            ·
              refine ⟨4644216629828765113901041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24769155359086747274138885 4644216629828765113901041)
              ·
                refine ⟨3483162472371573835425781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4644216629828765113901041 3483162472371573835425781)
                ·
                  refine ⟨326546481784835047071167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3483162472371573835425781 326546481784835047071167)
                  ·
                    rfl

theorem cell23_5723523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 5].length) (baseStart_5723523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723523 prefixEnd_5723523 := by exact prefixLift 5723523
  have htrace : WordTrace (prefixWord ++ tailWord_5723523) baseStart_5723523 baseEnd_5723523 := by
    simpa [prefixWord, tailWord_5723523, baseEnd_5723523] using wordTrace_append hprefix tailTrace_5723523
  have hstable : (prefixWord ++ tailWord_5723523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723523).length < 2 ^ (prefixWord ++ tailWord_5723523).sum := by decide
  have hdescent : baseEnd_5723523 < baseStart_5723523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723556 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_5723556 : Nat := 118140960795 + 5723556 * 2 ^ 59
def prefixEnd_5723556 : Nat := 4983230072969 + 3 ^ 40 * 5723556 * 2
def baseEnd_5723556 : Nat := 2938935280925113794527851

theorem tailTrace_5723556 : CollatzResearch.WordTrace tailWord_5723556 prefixEnd_5723556 2938935280925113794527851 := by
  unfold tailWord_5723556
  simp only [CollatzResearch.WordTrace]
  refine ⟨104377618626270796193359261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139170158168361061591145681 104377618626270796193359261)
  ·
    refine ⟨39141606984851548572509723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104377618626270796193359261 39141606984851548572509723)
    ·
      refine ⟨58712410477277322858764585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39141606984851548572509723 58712410477277322858764585)
      ·
        refine ⟨44034307857957992144073439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58712410477277322858764585 44034307857957992144073439)
        ·
          refine ⟨66051461786936988216110159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44034307857957992144073439 66051461786936988216110159)
          ·
            refine ⟨99077192680405482324165239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66051461786936988216110159 99077192680405482324165239)
            ·
              refine ⟨148615789020608223486247859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99077192680405482324165239 148615789020608223486247859)
              ·
                refine ⟨222923683530912335229371789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148615789020608223486247859 222923683530912335229371789)
                ·
                  refine ⟨83596381324092125711014421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222923683530912335229371789 83596381324092125711014421)
                  ·
                    refine ⟨3918580374566818392703801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83596381324092125711014421 3918580374566818392703801)
                    ·
                      refine ⟨2938935280925113794527851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918580374566818392703801 2938935280925113794527851)
                      ·
                        rfl

theorem cell23_5723556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_5723556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723556 prefixEnd_5723556 := by exact prefixLift 5723556
  have htrace : WordTrace (prefixWord ++ tailWord_5723556) baseStart_5723556 baseEnd_5723556 := by
    simpa [prefixWord, tailWord_5723556, baseEnd_5723556] using wordTrace_append hprefix tailTrace_5723556
  have hstable : (prefixWord ++ tailWord_5723556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723556).length < 2 ^ (prefixWord ++ tailWord_5723556).sum := by decide
  have hdescent : baseEnd_5723556 < baseStart_5723556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723569 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5723569 : Nat := 118140960795 + 5723569 * 2 ^ 59
def prefixEnd_5723569 : Nat := 4983230072969 + 3 ^ 40 * 5723569 * 2
def baseEnd_5723569 : Nat := 2938941956173622243665291

theorem tailTrace_5723569 : CollatzResearch.WordTrace tailWord_5723569 prefixEnd_5723569 2938941956173622243665291 := by
  unfold tailWord_5723569
  simp only [CollatzResearch.WordTrace]
  refine ⟨208755711401494495606941761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139170474267662997071294507 208755711401494495606941761)
  ·
    refine ⟨156566783551120871705206321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208755711401494495606941761 156566783551120871705206321)
    ·
      refine ⟨117425087663340653778904741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156566783551120871705206321 117425087663340653778904741)
      ·
        refine ⟨22017203936876372583544639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117425087663340653778904741 22017203936876372583544639)
        ·
          refine ⟨33025805905314558875316959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22017203936876372583544639 33025805905314558875316959)
          ·
            refine ⟨49538708857971838312975439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33025805905314558875316959 49538708857971838312975439)
            ·
              refine ⟨74308063286957757469463159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49538708857971838312975439 74308063286957757469463159)
              ·
                refine ⟨111462094930436636204194739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74308063286957757469463159 111462094930436636204194739)
                ·
                  refine ⟨167193142395654954306292109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111462094930436636204194739 167193142395654954306292109)
                  ·
                    refine ⟨62697428398370607864859541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167193142395654954306292109 62697428398370607864859541)
                    ·
                      refine ⟨2938941956173622243665291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62697428398370607864859541 2938941956173622243665291)
                      ·
                        rfl

theorem cell23_5723569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5723569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723569 prefixEnd_5723569 := by exact prefixLift 5723569
  have htrace : WordTrace (prefixWord ++ tailWord_5723569) baseStart_5723569 baseEnd_5723569 := by
    simpa [prefixWord, tailWord_5723569, baseEnd_5723569] using wordTrace_append hprefix tailTrace_5723569
  have hstable : (prefixWord ++ tailWord_5723569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723569).length < 2 ^ (prefixWord ++ tailWord_5723569).sum := by decide
  have hdescent : baseEnd_5723569 < baseStart_5723569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723573 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_5723573 : Nat := 118140960795 + 5723573 * 2 ^ 59
def prefixEnd_5723573 : Nat := 4983230072969 + 3 ^ 40 * 5723573 * 2
def baseEnd_5723573 : Nat := 2938944010096240228015273

theorem tailTrace_5723573 : CollatzResearch.WordTrace tailWord_5723573 prefixEnd_5723573 2938944010096240228015273 := by
  unfold tailWord_5723573
  simp only [CollatzResearch.WordTrace]
  refine ⟨208755857293480004290087373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139170571528986669526724915 208755857293480004290087373)
  ·
    refine ⟨78283446485055001608782765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208755857293480004290087373 78283446485055001608782765)
    ·
      refine ⟨29356292431895625603293537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78283446485055001608782765 29356292431895625603293537)
      ·
        refine ⟨22017219323921719202470153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29356292431895625603293537 22017219323921719202470153)
        ·
          refine ⟨16512914492941289401852615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22017219323921719202470153 16512914492941289401852615)
          ·
            refine ⟨24769371739411934102778923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16512914492941289401852615 24769371739411934102778923)
            ·
              refine ⟨37154057609117901154168385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24769371739411934102778923 37154057609117901154168385)
              ·
                refine ⟨27865543206838425865626289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37154057609117901154168385 27865543206838425865626289)
                ·
                  refine ⟨20899157405128819399219717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27865543206838425865626289 20899157405128819399219717)
                  ·
                    refine ⟨3918592013461653637353697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20899157405128819399219717 3918592013461653637353697)
                    ·
                      refine ⟨2938944010096240228015273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918592013461653637353697 2938944010096240228015273)
                      ·
                        rfl

theorem cell23_5723573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_5723573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723573 prefixEnd_5723573 := by exact prefixLift 5723573
  have htrace : WordTrace (prefixWord ++ tailWord_5723573) baseStart_5723573 baseEnd_5723573 := by
    simpa [prefixWord, tailWord_5723573, baseEnd_5723573] using wordTrace_append hprefix tailTrace_5723573
  have hstable : (prefixWord ++ tailWord_5723573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723573).length < 2 ^ (prefixWord ++ tailWord_5723573).sum := by decide
  have hdescent : baseEnd_5723573 < baseStart_5723573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723576 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_5723576 : Nat := 118140960795 + 5723576 * 2 ^ 59
def prefixEnd_5723576 : Nat := 4983230072969 + 3 ^ 40 * 5723576 * 2
def baseEnd_5723576 : Nat := 2938945550538203716277759

theorem tailTrace_5723576 : CollatzResearch.WordTrace tailWord_5723576 prefixEnd_5723576 2938945550538203716277759 := by
  unfold tailWord_5723576
  simp only [CollatzResearch.WordTrace]
  refine ⟨104377983356234567901223291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139170644474979423868297721 104377983356234567901223291)
  ·
    refine ⟨156566975034351851851834937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104377983356234567901223291 156566975034351851851834937)
    ·
      refine ⟨117425231275763888888876203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156566975034351851851834937 117425231275763888888876203)
      ·
        refine ⟨176137846913645833333314305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117425231275763888888876203 176137846913645833333314305)
        ·
          refine ⟨132103385185234374999985729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176137846913645833333314305 132103385185234374999985729)
          ·
            refine ⟨99077538888925781249989297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132103385185234374999985729 99077538888925781249989297)
            ·
              refine ⟨74308154166694335937491973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99077538888925781249989297 74308154166694335937491973)
              ·
                refine ⟨13932778906255187988279745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74308154166694335937491973 13932778906255187988279745)
                ·
                  refine ⟨10449584179691390991209809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13932778906255187988279745 10449584179691390991209809)
                  ·
                    refine ⟨7837188134768543243407357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10449584179691390991209809 7837188134768543243407357)
                    ·
                      refine ⟨2938945550538203716277759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7837188134768543243407357 2938945550538203716277759)
                      ·
                        rfl

theorem cell23_5723576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_5723576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723576 prefixEnd_5723576 := by exact prefixLift 5723576
  have htrace : WordTrace (prefixWord ++ tailWord_5723576) baseStart_5723576 baseEnd_5723576 := by
    simpa [prefixWord, tailWord_5723576, baseEnd_5723576] using wordTrace_append hprefix tailTrace_5723576
  have hstable : (prefixWord ++ tailWord_5723576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723576).length < 2 ^ (prefixWord ++ tailWord_5723576).sum := by decide
  have hdescent : baseEnd_5723576 < baseStart_5723576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723633 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 4, 3, 2]
def baseStart_5723633 : Nat := 118140960795 + 5723633 * 2 ^ 59
def prefixEnd_5723633 : Nat := 4983230072969 + 3 ^ 40 * 5723633 * 2
def baseEnd_5723633 : Nat := 2938974818935509993264997

theorem tailTrace_5723633 : CollatzResearch.WordTrace tailWord_5723633 prefixEnd_5723633 2938974818935509993264997 := by
  unfold tailWord_5723633
  simp only [CollatzResearch.WordTrace]
  refine ⟨208758045673262634537271553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139172030448841756358181035 208758045673262634537271553)
  ·
    refine ⟨156568534254946975902953665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208758045673262634537271553 156568534254946975902953665)
    ·
      refine ⟨117426400691210231927215249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156568534254946975902953665 117426400691210231927215249)
      ·
        refine ⟨88069800518407673945411437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117426400691210231927215249 88069800518407673945411437)
        ·
          refine ⟨33026175194402877729529289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88069800518407673945411437 33026175194402877729529289)
          ·
            refine ⟨24769631395802158297146967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33026175194402877729529289 24769631395802158297146967)
            ·
              refine ⟨37154447093703237445720451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24769631395802158297146967 37154447093703237445720451)
              ·
                refine ⟨55731670640554856168580677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37154447093703237445720451 55731670640554856168580677)
                ·
                  refine ⟨10449688245104035531608877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55731670640554856168580677 10449688245104035531608877)
                  ·
                    refine ⟨3918633091914013324353329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10449688245104035531608877 3918633091914013324353329)
                    ·
                      refine ⟨2938974818935509993264997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918633091914013324353329 2938974818935509993264997)
                      ·
                        rfl

theorem cell23_5723633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_5723633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723633 prefixEnd_5723633 := by exact prefixLift 5723633
  have htrace : WordTrace (prefixWord ++ tailWord_5723633) baseStart_5723633 baseEnd_5723633 := by
    simpa [prefixWord, tailWord_5723633, baseEnd_5723633] using wordTrace_append hprefix tailTrace_5723633
  have hstable : (prefixWord ++ tailWord_5723633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723633).length < 2 ^ (prefixWord ++ tailWord_5723633).sum := by decide
  have hdescent : baseEnd_5723633 < baseStart_5723633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723639 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 5, 6]
def baseStart_5723639 : Nat := 118140960795 + 5723639 * 2 ^ 59
def prefixEnd_5723639 : Nat := 4983230072969 + 3 ^ 40 * 5723639 * 2
def baseEnd_5723639 : Nat := 979659299939812323263323

theorem tailTrace_5723639 : CollatzResearch.WordTrace tailWord_5723639 prefixEnd_5723639 979659299939812323263323 := by
  unfold tailWord_5723639
  simp only [CollatzResearch.WordTrace]
  refine ⟨208758264511240897561989971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139172176340827265041326647 208758264511240897561989971)
  ·
    refine ⟨313137396766861346342984957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208758264511240897561989971 313137396766861346342984957)
    ·
      refine ⟨117426523787573004878619359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313137396766861346342984957 117426523787573004878619359)
      ·
        refine ⟨176139785681359507317929039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117426523787573004878619359 176139785681359507317929039)
        ·
          refine ⟨264209678522039260976893559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176139785681359507317929039 264209678522039260976893559)
          ·
            refine ⟨396314517783058891465340339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264209678522039260976893559 396314517783058891465340339)
            ·
              refine ⟨594471776674588337198010509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396314517783058891465340339 594471776674588337198010509)
              ·
                refine ⟨222926916252970626449253941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594471776674588337198010509 222926916252970626449253941)
                ·
                  refine ⟨20899398398715996229617557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222926916252970626449253941 20899398398715996229617557)
                  ·
                    refine ⟨979659299939812323263323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20899398398715996229617557 979659299939812323263323)
                    ·
                      rfl

theorem cell23_5723639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_5723639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723639 prefixEnd_5723639 := by exact prefixLift 5723639
  have htrace : WordTrace (prefixWord ++ tailWord_5723639) baseStart_5723639 baseEnd_5723639 := by
    simpa [prefixWord, tailWord_5723639, baseEnd_5723639] using wordTrace_append hprefix tailTrace_5723639
  have hstable : (prefixWord ++ tailWord_5723639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723639).length < 2 ^ (prefixWord ++ tailWord_5723639).sum := by decide
  have hdescent : baseEnd_5723639 < baseStart_5723639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723640 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_5723640 : Nat := 118140960795 + 5723640 * 2 ^ 59
def prefixEnd_5723640 : Nat := 4983230072969 + 3 ^ 40 * 5723640 * 2
def baseEnd_5723640 : Nat := 2938978413300091465877465

theorem tailTrace_5723640 : CollatzResearch.WordTrace tailWord_5723640 prefixEnd_5723640 2938978413300091465877465 := by
  unfold tailWord_5723640
  simp only [CollatzResearch.WordTrace]
  refine ⟨104379150492118637366388187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139172200656158183155184249 104379150492118637366388187)
  ·
    refine ⟨156568725738177956049582281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104379150492118637366388187 156568725738177956049582281)
    ·
      refine ⟨117426544303633467037186711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156568725738177956049582281 117426544303633467037186711)
      ·
        refine ⟨176139816455450200555780067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117426544303633467037186711 176139816455450200555780067)
        ·
          refine ⟨264209724683175300833670101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176139816455450200555780067 264209724683175300833670101)
          ·
            refine ⟨6192415422261921113289143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 264209724683175300833670101 6192415422261921113289143)
            ·
              refine ⟨9288623133392881669933715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192415422261921113289143 9288623133392881669933715)
              ·
                refine ⟨13932934700089322504900573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288623133392881669933715 13932934700089322504900573)
                ·
                  refine ⟨5224850512533495939337715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13932934700089322504900573 5224850512533495939337715)
                  ·
                    refine ⟨7837275768800243909006573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5224850512533495939337715 7837275768800243909006573)
                    ·
                      refine ⟨2938978413300091465877465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7837275768800243909006573 2938978413300091465877465)
                      ·
                        rfl

theorem cell23_5723640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_5723640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723640 prefixEnd_5723640 := by exact prefixLift 5723640
  have htrace : WordTrace (prefixWord ++ tailWord_5723640) baseStart_5723640 baseEnd_5723640 := by
    simpa [prefixWord, tailWord_5723640, baseEnd_5723640] using wordTrace_append hprefix tailTrace_5723640
  have hstable : (prefixWord ++ tailWord_5723640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723640).length < 2 ^ (prefixWord ++ tailWord_5723640).sum := by decide
  have hdescent : baseEnd_5723640 < baseStart_5723640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723660 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_5723660 : Nat := 118140960795 + 5723660 * 2 ^ 59
def prefixEnd_5723660 : Nat := 4983230072969 + 3 ^ 40 * 5723660 * 2
def baseEnd_5723660 : Nat := 979662894304393795875791

theorem tailTrace_5723660 : CollatzResearch.WordTrace tailWord_5723660 prefixEnd_5723660 979662894304393795875791 := by
  unfold tailWord_5723660
  simp only [CollatzResearch.WordTrace]
  refine ⟨104379515222082409074252217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139172686962776545432336289 104379515222082409074252217)
  ·
    refine ⟨78284636416561806805689163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104379515222082409074252217 78284636416561806805689163)
    ·
      refine ⟨117426954624842710208533745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78284636416561806805689163 117426954624842710208533745)
      ·
        refine ⟨88070215968632032656400309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117426954624842710208533745 88070215968632032656400309)
        ·
          refine ⟨8256582747059253061537529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88070215968632032656400309 8256582747059253061537529)
          ·
            refine ⟨6192437060294439796153147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8256582747059253061537529 6192437060294439796153147)
            ·
              refine ⟨9288655590441659694229721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192437060294439796153147 9288655590441659694229721)
              ·
                refine ⟨6966491692831244770672291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9288655590441659694229721 6966491692831244770672291)
                ·
                  refine ⟨10449737539246867156008437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6966491692831244770672291 10449737539246867156008437)
                  ·
                    refine ⟨979662894304393795875791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10449737539246867156008437 979662894304393795875791)
                    ·
                      rfl

theorem cell23_5723660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_5723660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723660 prefixEnd_5723660 := by exact prefixLift 5723660
  have htrace : WordTrace (prefixWord ++ tailWord_5723660) baseStart_5723660 baseEnd_5723660 := by
    simpa [prefixWord, tailWord_5723660, baseEnd_5723660] using wordTrace_append hprefix tailTrace_5723660
  have hstable : (prefixWord ++ tailWord_5723660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723660).length < 2 ^ (prefixWord ++ tailWord_5723660).sum := by decide
  have hdescent : baseEnd_5723660 < baseStart_5723660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723689 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_5723689 : Nat := 118140960795 + 5723689 * 2 ^ 59
def prefixEnd_5723689 : Nat := 4983230072969 + 3 ^ 40 * 5723689 * 2
def baseEnd_5723689 : Nat := 2939003573852161774164739

theorem tailTrace_5723689 : CollatzResearch.WordTrace tailWord_5723689 prefixEnd_5723689 2939003573852161774164739 := by
  unfold tailWord_5723689
  simp only [CollatzResearch.WordTrace]
  refine ⟨208760088161059756101310121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139173392107373170734206747 208760088161059756101310121)
  ·
    refine ⟨156570066120794817075982591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208760088161059756101310121 156570066120794817075982591)
    ·
      refine ⟨234855099181192225613973887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156570066120794817075982591 234855099181192225613973887)
      ·
        refine ⟨352282648771788338420960831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234855099181192225613973887 352282648771788338420960831)
        ·
          refine ⟨528423973157682507631441247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352282648771788338420960831 528423973157682507631441247)
          ·
            refine ⟨792635959736523761447161871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528423973157682507631441247 792635959736523761447161871)
            ·
              refine ⟨1188953939604785642170742807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792635959736523761447161871 1188953939604785642170742807)
              ·
                refine ⟨1783430909407178463256114211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188953939604785642170742807 1783430909407178463256114211)
                ·
                  refine ⟨2675146364110767694884171317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783430909407178463256114211 2675146364110767694884171317)
                  ·
                    refine ⟨250794971635384471395391061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2675146364110767694884171317 250794971635384471395391061)
                    ·
                      refine ⟨2939003573852161774164739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250794971635384471395391061 2939003573852161774164739)
                      ·
                        rfl

theorem cell23_5723689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_5723689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723689 prefixEnd_5723689 := by exact prefixLift 5723689
  have htrace : WordTrace (prefixWord ++ tailWord_5723689) baseStart_5723689 baseEnd_5723689 := by
    simpa [prefixWord, tailWord_5723689, baseEnd_5723689] using wordTrace_append hprefix tailTrace_5723689
  have hstable : (prefixWord ++ tailWord_5723689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723689).length < 2 ^ (prefixWord ++ tailWord_5723689).sum := by decide
  have hdescent : baseEnd_5723689 < baseStart_5723689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723690 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_5723690 : Nat := 118140960795 + 5723690 * 2 ^ 59
def prefixEnd_5723690 : Nat := 4983230072969 + 3 ^ 40 * 5723690 * 2
def baseEnd_5723690 : Nat := 979668029110938756750745

theorem tailTrace_5723690 : CollatzResearch.WordTrace tailWord_5723690 prefixEnd_5723690 979668029110938756750745 := by
  unfold tailWord_5723690
  simp only [CollatzResearch.WordTrace]
  refine ⟨52190031158514033318024131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139173416422704088848064349 52190031158514033318024131)
  ·
    refine ⟨78285046737771049977036197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52190031158514033318024131 78285046737771049977036197)
    ·
      refine ⟨14678446263332071870694287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78285046737771049977036197 14678446263332071870694287)
      ·
        refine ⟨22017669394998107806041431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14678446263332071870694287 22017669394998107806041431)
        ·
          refine ⟨33026504092497161709062147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22017669394998107806041431 33026504092497161709062147)
          ·
            refine ⟨49539756138745742563593221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33026504092497161709062147 49539756138745742563593221)
            ·
              refine ⟨9288704276014826730673729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49539756138745742563593221 9288704276014826730673729)
              ·
                refine ⟨6966528207011120048005297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9288704276014826730673729 6966528207011120048005297)
                ·
                  refine ⟨5224896155258340036003973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6966528207011120048005297 5224896155258340036003973)
                  ·
                    refine ⟨979668029110938756750745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5224896155258340036003973 979668029110938756750745)
                    ·
                      rfl

theorem cell23_5723690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_5723690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723690 prefixEnd_5723690 := by exact prefixLift 5723690
  have htrace : WordTrace (prefixWord ++ tailWord_5723690) baseStart_5723690 baseEnd_5723690 := by
    simpa [prefixWord, tailWord_5723690, baseEnd_5723690] using wordTrace_append hprefix tailTrace_5723690
  have hstable : (prefixWord ++ tailWord_5723690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723690).length < 2 ^ (prefixWord ++ tailWord_5723690).sum := by decide
  have hdescent : baseEnd_5723690 < baseStart_5723690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723696 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_5723696 : Nat := 118140960795 + 5723696 * 2 ^ 59
def prefixEnd_5723696 : Nat := 4983230072969 + 3 ^ 40 * 5723696 * 2
def baseEnd_5723696 : Nat := 2939007168216743246777207

theorem tailTrace_5723696 : CollatzResearch.WordTrace tailWord_5723696 prefixEnd_5723696 2939007168216743246777207 := by
  unfold tailWord_5723696
  simp only [CollatzResearch.WordTrace]
  refine ⟨104380171736017198148407471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139173562314689597531209961 104380171736017198148407471)
  ·
    refine ⟨156570257604025797222611207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104380171736017198148407471 156570257604025797222611207)
    ·
      refine ⟨234855386406038695833916811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156570257604025797222611207 234855386406038695833916811)
      ·
        refine ⟨352283079609058043750875217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234855386406038695833916811 352283079609058043750875217)
        ·
          refine ⟨264212309706793532813156413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352283079609058043750875217 264212309706793532813156413)
          ·
            refine ⟨99079616140047574804933655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264212309706793532813156413 99079616140047574804933655)
            ·
              refine ⟨148619424210071362207400483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99079616140047574804933655 148619424210071362207400483)
              ·
                refine ⟨222929136315107043311100725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148619424210071362207400483 222929136315107043311100725)
                ·
                  refine ⟨20899606529541285310415693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222929136315107043311100725 20899606529541285310415693)
                  ·
                    refine ⟨7837352448577981991405885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20899606529541285310415693 7837352448577981991405885)
                    ·
                      refine ⟨2939007168216743246777207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7837352448577981991405885 2939007168216743246777207)
                      ·
                        rfl

theorem cell23_5723696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_5723696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723696 prefixEnd_5723696 := by exact prefixLift 5723696
  have htrace : WordTrace (prefixWord ++ tailWord_5723696) baseStart_5723696 baseEnd_5723696 := by
    simpa [prefixWord, tailWord_5723696, baseEnd_5723696] using wordTrace_append hprefix tailTrace_5723696
  have hstable : (prefixWord ++ tailWord_5723696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723696).length < 2 ^ (prefixWord ++ tailWord_5723696).sum := by decide
  have hdescent : baseEnd_5723696 < baseStart_5723696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723726 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_5723726 : Nat := 118140960795 + 5723726 * 2 ^ 59
def prefixEnd_5723726 : Nat := 4983230072969 + 3 ^ 40 * 5723726 * 2
def baseEnd_5723726 : Nat := 2939022572636378129402069

theorem tailTrace_5723726 : CollatzResearch.WordTrace tailWord_5723726 prefixEnd_5723726 2939022572636378129402069 := by
  unfold tailWord_5723726
  simp only [CollatzResearch.WordTrace]
  refine ⟨26095179707740713927550879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139174291774617140946938021 26095179707740713927550879)
  ·
    refine ⟨39142769561611070891326319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26095179707740713927550879 39142769561611070891326319)
    ·
      refine ⟨58714154342416606336989479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39142769561611070891326319 58714154342416606336989479)
      ·
        refine ⟨88071231513624909505484219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58714154342416606336989479 88071231513624909505484219)
        ·
          refine ⟨132106847270437364258226329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88071231513624909505484219 132106847270437364258226329)
          ·
            refine ⟨99080135452828023193669747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132106847270437364258226329 99080135452828023193669747)
            ·
              refine ⟨148620203179242034790504621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99080135452828023193669747 148620203179242034790504621)
              ·
                refine ⟨55732576192215763046439233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148620203179242034790504621 55732576192215763046439233)
                ·
                  refine ⟨41799432144161822284829425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55732576192215763046439233 41799432144161822284829425)
                  ·
                    refine ⟨31349574108121366713622069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41799432144161822284829425 31349574108121366713622069)
                    ·
                      refine ⟨2939022572636378129402069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31349574108121366713622069 2939022572636378129402069)
                      ·
                        rfl

theorem cell23_5723726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_5723726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723726 prefixEnd_5723726 := by exact prefixLift 5723726
  have htrace : WordTrace (prefixWord ++ tailWord_5723726) baseStart_5723726 baseEnd_5723726 := by
    simpa [prefixWord, tailWord_5723726, baseEnd_5723726] using wordTrace_append hprefix tailTrace_5723726
  have hstable : (prefixWord ++ tailWord_5723726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723726).length < 2 ^ (prefixWord ++ tailWord_5723726).sum := by decide
  have hdescent : baseEnd_5723726 < baseStart_5723726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723741 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5723741 : Nat := 118140960795 + 5723741 * 2 ^ 59
def prefixEnd_5723741 : Nat := 4983230072969 + 3 ^ 40 * 5723741 * 2
def baseEnd_5723741 : Nat := 979676758282065190238167

theorem tailTrace_5723741 : CollatzResearch.WordTrace tailWord_5723741 prefixEnd_5723741 979676758282065190238167 := by
  unfold tailWord_5723741
  simp only [CollatzResearch.WordTrace]
  refine ⟨208761984756871368982203077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139174656504580912654802051 208761984756871368982203077)
  ·
    refine ⟨39142872141913381684163077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208761984756871368982203077 39142872141913381684163077)
    ·
      refine ⟨7339288526608759065780577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39142872141913381684163077 7339288526608759065780577)
      ·
        refine ⟨5504466394956569299335433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7339288526608759065780577 5504466394956569299335433)
        ·
          refine ⟨4128349796217426974501575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5504466394956569299335433 4128349796217426974501575)
          ·
            refine ⟨6192524694326140461752363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128349796217426974501575 6192524694326140461752363)
            ·
              refine ⟨9288787041489210692628545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192524694326140461752363 9288787041489210692628545)
              ·
                refine ⟨6966590281116908019471409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9288787041489210692628545 6966590281116908019471409)
                ·
                  refine ⟨5224942710837681014603557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6966590281116908019471409 5224942710837681014603557)
                  ·
                    refine ⟨979676758282065190238167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5224942710837681014603557 979676758282065190238167)
                    ·
                      rfl

theorem cell23_5723741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5723741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723741 prefixEnd_5723741 := by exact prefixLift 5723741
  have htrace : WordTrace (prefixWord ++ tailWord_5723741) baseStart_5723741 baseEnd_5723741 := by
    simpa [prefixWord, tailWord_5723741, baseEnd_5723741] using wordTrace_append hprefix tailTrace_5723741
  have hstable : (prefixWord ++ tailWord_5723741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723741).length < 2 ^ (prefixWord ++ tailWord_5723741).sum := by decide
  have hdescent : baseEnd_5723741 < baseStart_5723741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723747 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 3]
def baseStart_5723747 : Nat := 118140960795 + 5723747 * 2 ^ 59
def prefixEnd_5723747 : Nat := 4983230072969 + 3 ^ 40 * 5723747 * 2
def baseEnd_5723747 : Nat := 2939033355730122547239473

theorem tailTrace_5723747 : CollatzResearch.WordTrace tailWord_5723747 prefixEnd_5723747 2939033355730122547239473 := by
  unfold tailWord_5723747
  simp only [CollatzResearch.WordTrace]
  refine ⟨208762203594849632006921495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139174802396566421337947663 208762203594849632006921495)
  ·
    refine ⟨313143305392274448010382243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208762203594849632006921495 313143305392274448010382243)
    ·
      refine ⟨469714958088411672015573365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313143305392274448010382243 469714958088411672015573365)
      ·
        refine ⟨44035777320788594251460003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 469714958088411672015573365 44035777320788594251460003)
        ·
          refine ⟨66053665981182891377190005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44035777320788594251460003 66053665981182891377190005)
          ·
            refine ⟨6192531185735896066611563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66053665981182891377190005 6192531185735896066611563)
            ·
              refine ⟨9288796778603844099917345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192531185735896066611563 9288796778603844099917345)
              ·
                refine ⟨6966597583952883074938009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9288796778603844099917345 6966597583952883074938009)
                ·
                  refine ⟨5224948187964662306203507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6966597583952883074938009 5224948187964662306203507)
                  ·
                    refine ⟨7837422281946993459305261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5224948187964662306203507 7837422281946993459305261)
                    ·
                      refine ⟨2939033355730122547239473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7837422281946993459305261 2939033355730122547239473)
                      ·
                        rfl

theorem cell23_5723747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_5723747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723747 prefixEnd_5723747 := by exact prefixLift 5723747
  have htrace : WordTrace (prefixWord ++ tailWord_5723747) baseStart_5723747 baseEnd_5723747 := by
    simpa [prefixWord, tailWord_5723747, baseEnd_5723747] using wordTrace_append hprefix tailTrace_5723747
  have hstable : (prefixWord ++ tailWord_5723747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723747).length < 2 ^ (prefixWord ++ tailWord_5723747).sum := by decide
  have hdescent : baseEnd_5723747 < baseStart_5723747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723753 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 3, 4, 2]
def baseStart_5723753 : Nat := 118140960795 + 5723753 * 2 ^ 59
def prefixEnd_5723753 : Nat := 4983230072969 + 3 ^ 40 * 5723753 * 2
def baseEnd_5723753 : Nat := 2939036436614049523764445

theorem tailTrace_5723753 : CollatzResearch.WordTrace tailWord_5723753 prefixEnd_5723753 2939036436614049523764445 := by
  unfold tailWord_5723753
  simp only [CollatzResearch.WordTrace]
  refine ⟨208762422432827895031639913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139174948288551930021093275 208762422432827895031639913)
  ·
    refine ⟨156571816824620921273729935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208762422432827895031639913 156571816824620921273729935)
    ·
      refine ⟨234857725236931381910594903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156571816824620921273729935 234857725236931381910594903)
      ·
        refine ⟨352286587855397072865892355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234857725236931381910594903 352286587855397072865892355)
        ·
          refine ⟨528429881783095609298838533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352286587855397072865892355 528429881783095609298838533)
          ·
            refine ⟨99080602834330426743532225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 528429881783095609298838533 99080602834330426743532225)
            ·
              refine ⟨74310452125747820057649169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99080602834330426743532225 74310452125747820057649169)
              ·
                refine ⟨55732839094310865043236877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74310452125747820057649169 55732839094310865043236877)
                ·
                  refine ⟨20899814660366574391213829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55732839094310865043236877 20899814660366574391213829)
                  ·
                    refine ⟨3918715248818732698352593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20899814660366574391213829 3918715248818732698352593)
                    ·
                      refine ⟨2939036436614049523764445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918715248818732698352593 2939036436614049523764445)
                      ·
                        rfl

theorem cell23_5723753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 4, 2].length) (baseStart_5723753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723753 prefixEnd_5723753 := by exact prefixLift 5723753
  have htrace : WordTrace (prefixWord ++ tailWord_5723753) baseStart_5723753 baseEnd_5723753 := by
    simpa [prefixWord, tailWord_5723753, baseEnd_5723753] using wordTrace_append hprefix tailTrace_5723753
  have hstable : (prefixWord ++ tailWord_5723753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723753).length < 2 ^ (prefixWord ++ tailWord_5723753).sum := by decide
  have hdescent : baseEnd_5723753 < baseStart_5723753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723756 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_5723756 : Nat := 118140960795 + 5723756 * 2 ^ 59
def prefixEnd_5723756 : Nat := 4983230072969 + 3 ^ 40 * 5723756 * 2
def baseEnd_5723756 : Nat := 2939037977056013012026931

theorem tailTrace_5723756 : CollatzResearch.WordTrace tailWord_5723756 prefixEnd_5723756 2939037977056013012026931 := by
  unfold tailWord_5723756
  simp only [CollatzResearch.WordTrace]
  refine ⟨104381265925908513271999561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139175021234544684362666081 104381265925908513271999561)
  ·
    refine ⟨78285949444431384953999671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104381265925908513271999561 78285949444431384953999671)
    ·
      refine ⟨117428924166647077430999507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78285949444431384953999671 117428924166647077430999507)
      ·
        refine ⟨176143386249970616146499261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117428924166647077430999507 176143386249970616146499261)
        ·
          refine ⟨66053769843738981054937223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176143386249970616146499261 66053769843738981054937223)
          ·
            refine ⟨99080654765608471582405835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66053769843738981054937223 99080654765608471582405835)
            ·
              refine ⟨148620982148412707373608753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99080654765608471582405835 148620982148412707373608753)
              ·
                refine ⟨111465736611309530530206565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148620982148412707373608753 111465736611309530530206565)
                ·
                  refine ⟨20899825614620536974413731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111465736611309530530206565 20899825614620536974413731)
                  ·
                    refine ⟨31349738421930805461620597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20899825614620536974413731 31349738421930805461620597)
                    ·
                      refine ⟨2939037977056013012026931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31349738421930805461620597 2939037977056013012026931)
                      ·
                        rfl

theorem cell23_5723756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_5723756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723756 prefixEnd_5723756 := by exact prefixLift 5723756
  have htrace : WordTrace (prefixWord ++ tailWord_5723756) baseStart_5723756 baseEnd_5723756 := by
    simpa [prefixWord, tailWord_5723756, baseEnd_5723756] using wordTrace_append hprefix tailTrace_5723756
  have hstable : (prefixWord ++ tailWord_5723756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723756).length < 2 ^ (prefixWord ++ tailWord_5723756).sum := by decide
  have hdescent : baseEnd_5723756 < baseStart_5723756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723776 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 7]
def baseStart_5723776 : Nat := 118140960795 + 5723776 * 2 ^ 59
def prefixEnd_5723776 : Nat := 4983230072969 + 3 ^ 40 * 5723776 * 2
def baseEnd_5723776 : Nat := 326560916296566992641871

theorem tailTrace_5723776 : CollatzResearch.WordTrace tailWord_5723776 prefixEnd_5723776 326560916296566992641871 := by
  unfold tailWord_5723776
  simp only [CollatzResearch.WordTrace]
  refine ⟨104381630655872284979863591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139175507541163046639818121 104381630655872284979863591)
  ·
    refine ⟨156572445983808427469795387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104381630655872284979863591 156572445983808427469795387)
    ·
      refine ⟨234858668975712641204693081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156572445983808427469795387 234858668975712641204693081)
      ·
        refine ⟨176144001731784480903519811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234858668975712641204693081 176144001731784480903519811)
        ·
          refine ⟨264216002597676721355279717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176144001731784480903519811 264216002597676721355279717)
          ·
            refine ⟨49540500487064385254114947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264216002597676721355279717 49540500487064385254114947)
            ·
              refine ⟨74310750730596577881172421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49540500487064385254114947 74310750730596577881172421)
              ·
                refine ⟨13933265761986858352719829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74310750730596577881172421 13933265761986858352719829)
                ·
                  refine ⟨326560916296566992641871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13933265761986858352719829 326560916296566992641871)
                  ·
                    rfl

theorem cell23_5723776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_5723776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723776 prefixEnd_5723776 := by exact prefixLift 5723776
  have htrace : WordTrace (prefixWord ++ tailWord_5723776) baseStart_5723776 baseEnd_5723776 := by
    simpa [prefixWord, tailWord_5723776, baseEnd_5723776] using wordTrace_append hprefix tailTrace_5723776
  have hstable : (prefixWord ++ tailWord_5723776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723776).length < 2 ^ (prefixWord ++ tailWord_5723776).sum := by decide
  have hdescent : baseEnd_5723776 < baseStart_5723776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723793 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 5]
def baseStart_5723793 : Nat := 118140960795 + 5723793 * 2 ^ 59
def prefixEnd_5723793 : Nat := 4983230072969 + 3 ^ 40 * 5723793 * 2
def baseEnd_5723793 : Nat := 326561886204469929696029

theorem tailTrace_5723793 : CollatzResearch.WordTrace tailWord_5723793 prefixEnd_5723793 326561886204469929696029 := by
  unfold tailWord_5723793
  simp only [CollatzResearch.WordTrace]
  refine ⟨208763881352682981863096033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139175920901788654575397355 208763881352682981863096033)
  ·
    refine ⟨156572911014512236397322025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208763881352682981863096033 156572911014512236397322025)
    ·
      refine ⟨117429683260884177297991519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156572911014512236397322025 117429683260884177297991519)
      ·
        refine ⟨176144524891326265946987279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117429683260884177297991519 176144524891326265946987279)
        ·
          refine ⟨264216787336989398920480919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176144524891326265946987279 264216787336989398920480919)
          ·
            refine ⟨396325181005484098380721379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264216787336989398920480919 396325181005484098380721379)
            ·
              refine ⟨594487771508226147571082069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396325181005484098380721379 594487771508226147571082069)
              ·
                refine ⟨3483326786181012583424309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 594487771508226147571082069 3483326786181012583424309)
                ·
                  refine ⟨326561886204469929696029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3483326786181012583424309 326561886204469929696029)
                  ·
                    rfl

theorem cell23_5723793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 5].length) (baseStart_5723793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723793 prefixEnd_5723793 := by exact prefixLift 5723793
  have htrace : WordTrace (prefixWord ++ tailWord_5723793) baseStart_5723793 baseEnd_5723793 := by
    simpa [prefixWord, tailWord_5723793, baseEnd_5723793] using wordTrace_append hprefix tailTrace_5723793
  have hstable : (prefixWord ++ tailWord_5723793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723793).length < 2 ^ (prefixWord ++ tailWord_5723793).sum := by decide
  have hdescent : baseEnd_5723793 < baseStart_5723793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723883 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 6]
def baseStart_5723883 : Nat := 118140960795 + 5723883 * 2 ^ 59
def prefixEnd_5723883 : Nat := 4983230072969 + 3 ^ 40 * 5723883 * 2
def baseEnd_5723883 : Nat := 326567021011014890570983

theorem tailTrace_5723883 : CollatzResearch.WordTrace tailWord_5723883 prefixEnd_5723883 326567021011014890570983 := by
  unfold tailWord_5723883
  simp only [CollatzResearch.WordTrace]
  refine ⟨208767163922356927233872303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139178109281571284822581535 208767163922356927233872303)
  ·
    refine ⟨313150745883535390850808455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208767163922356927233872303 313150745883535390850808455)
    ·
      refine ⟨469726118825303086276212683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313150745883535390850808455 469726118825303086276212683)
      ·
        refine ⟨704589178237954629414319025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469726118825303086276212683 704589178237954629414319025)
        ·
          refine ⟨528441883678465972060739269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704589178237954629414319025 528441883678465972060739269)
          ·
            refine ⟨99082853189712369761388613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 528441883678465972060739269 99082853189712369761388613)
            ·
              refine ⟨18578034973071069330260365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99082853189712369761388613 18578034973071069330260365)
              ·
                refine ⟨6966763114901650998847637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18578034973071069330260365 6966763114901650998847637)
                ·
                  refine ⟨326567021011014890570983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6966763114901650998847637 326567021011014890570983)
                  ·
                    rfl

theorem cell23_5723883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 6].length) (baseStart_5723883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723883 prefixEnd_5723883 := by exact prefixLift 5723883
  have htrace : WordTrace (prefixWord ++ tailWord_5723883) baseStart_5723883 baseEnd_5723883 := by
    simpa [prefixWord, tailWord_5723883, baseEnd_5723883] using wordTrace_append hprefix tailTrace_5723883
  have hstable : (prefixWord ++ tailWord_5723883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723883).length < 2 ^ (prefixWord ++ tailWord_5723883).sum := by decide
  have hdescent : baseEnd_5723883 < baseStart_5723883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723927 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_5723927 : Nat := 118140960795 + 5723927 * 2 ^ 59
def prefixEnd_5723927 : Nat := 4983230072969 + 3 ^ 40 * 5723927 * 2
def baseEnd_5723927 : Nat := 2939125782247931842988645

theorem tailTrace_5723927 : CollatzResearch.WordTrace tailWord_5723927 prefixEnd_5723927 2939125782247931842988645 := by
  unfold tailWord_5723927
  simp only [CollatzResearch.WordTrace]
  refine ⟨208768768734197522748474035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139179179156131681832316023 208768768734197522748474035)
  ·
    refine ⟨313153153101296284122711053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208768768734197522748474035 313153153101296284122711053)
    ·
      refine ⟨117432432412986106546016645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313153153101296284122711053 117432432412986106546016645)
      ·
        refine ⟨22018581077434894977378121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117432432412986106546016645 22018581077434894977378121)
        ·
          refine ⟨16513935808076171233033591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22018581077434894977378121 16513935808076171233033591)
          ·
            refine ⟨24770903712114256849550387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16513935808076171233033591 24770903712114256849550387)
            ·
              refine ⟨37156355568171385274325581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24770903712114256849550387 37156355568171385274325581)
              ·
                refine ⟨13933633338064269477872093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37156355568171385274325581 13933633338064269477872093)
                ·
                  refine ⟨5225112501774101054202035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13933633338064269477872093 5225112501774101054202035)
                  ·
                    refine ⟨7837668752661151581303053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225112501774101054202035 7837668752661151581303053)
                    ·
                      refine ⟨2939125782247931842988645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7837668752661151581303053 2939125782247931842988645)
                      ·
                        rfl

theorem cell23_5723927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_5723927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723927 prefixEnd_5723927 := by exact prefixLift 5723927
  have htrace : WordTrace (prefixWord ++ tailWord_5723927) baseStart_5723927 baseEnd_5723927 := by
    simpa [prefixWord, tailWord_5723927, baseEnd_5723927] using wordTrace_append hprefix tailTrace_5723927
  have hstable : (prefixWord ++ tailWord_5723927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723927).length < 2 ^ (prefixWord ++ tailWord_5723927).sum := by decide
  have hdescent : baseEnd_5723927 < baseStart_5723927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723960 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 4, 4]
def baseStart_5723960 : Nat := 118140960795 + 5723960 * 2 ^ 59
def prefixEnd_5723960 : Nat := 4983230072969 + 3 ^ 40 * 5723960 * 2
def baseEnd_5723960 : Nat := 979714242369843404625331

theorem tailTrace_5723960 : CollatzResearch.WordTrace tailWord_5723960 prefixEnd_5723960 979714242369843404625331 := by
  unfold tailWord_5723960
  simp only [CollatzResearch.WordTrace]
  refine ⟨104384986171538984692212667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139179981562051979589616889 104384986171538984692212667)
  ·
    refine ⟨156577479257308477038319001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104384986171538984692212667 156577479257308477038319001)
    ·
      refine ⟨117433109442981357778739251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156577479257308477038319001 117433109442981357778739251)
      ·
        refine ⟨176149664164472036668108877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117433109442981357778739251 176149664164472036668108877)
        ·
          refine ⟨66056124061677013750540829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176149664164472036668108877 66056124061677013750540829)
          ·
            refine ⟨24771046523128880156452811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66056124061677013750540829 24771046523128880156452811)
            ·
              refine ⟨37156569784693320234679217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24771046523128880156452811 37156569784693320234679217)
              ·
                refine ⟨27867427338519990176009413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37156569784693320234679217 27867427338519990176009413)
                ·
                  refine ⟨5225142625972498158001765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27867427338519990176009413 5225142625972498158001765)
                  ·
                    refine ⟨979714242369843404625331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225142625972498158001765 979714242369843404625331)
                    ·
                      rfl

theorem cell23_5723960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_5723960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723960 prefixEnd_5723960 := by exact prefixLift 5723960
  have htrace : WordTrace (prefixWord ++ tailWord_5723960) baseStart_5723960 baseEnd_5723960 := by
    simpa [prefixWord, tailWord_5723960, baseEnd_5723960] using wordTrace_append hprefix tailTrace_5723960
  have hstable : (prefixWord ++ tailWord_5723960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723960).length < 2 ^ (prefixWord ++ tailWord_5723960).sum := by decide
  have hdescent : baseEnd_5723960 < baseStart_5723960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5723993 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_5723993 : Nat := 118140960795 + 5723993 * 2 ^ 59
def prefixEnd_5723993 : Nat := 4983230072969 + 3 ^ 40 * 5723993 * 2
def baseEnd_5723993 : Nat := 2939159671971128584763341

theorem tailTrace_5723993 : CollatzResearch.WordTrace tailWord_5723993 prefixEnd_5723993 2939159671971128584763341 := by
  unfold tailWord_5723993
  simp only [CollatzResearch.WordTrace]
  refine ⟨208771175951958416020376633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139180783967972277346917755 208771175951958416020376633)
  ·
    refine ⟨156578381963968812015282475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208771175951958416020376633 156578381963968812015282475)
    ·
      refine ⟨234867572945953218022923713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156578381963968812015282475 234867572945953218022923713)
      ·
        refine ⟨176150679709464913517192785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234867572945953218022923713 176150679709464913517192785)
        ·
          refine ⟨132113009782098685137894589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176150679709464913517192785 132113009782098685137894589)
          ·
            refine ⟨49542378668287006926710471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132113009782098685137894589 49542378668287006926710471)
            ·
              refine ⟨74313568002430510390065707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49542378668287006926710471 74313568002430510390065707)
              ·
                refine ⟨111470352003645765585098561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74313568002430510390065707 111470352003645765585098561)
                ·
                  refine ⟨83602764002734324188823921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111470352003645765585098561 83602764002734324188823921)
                  ·
                    refine ⟨62702073002050743141617941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83602764002734324188823921 62702073002050743141617941)
                    ·
                      refine ⟨2939159671971128584763341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62702073002050743141617941 2939159671971128584763341)
                      ·
                        rfl

theorem cell23_5723993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_5723993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5723993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5723993 prefixEnd_5723993 := by exact prefixLift 5723993
  have htrace : WordTrace (prefixWord ++ tailWord_5723993) baseStart_5723993 baseEnd_5723993 := by
    simpa [prefixWord, tailWord_5723993, baseEnd_5723993] using wordTrace_append hprefix tailTrace_5723993
  have hstable : (prefixWord ++ tailWord_5723993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5723993).length < 2 ^ (prefixWord ++ tailWord_5723993).sum := by decide
  have hdescent : baseEnd_5723993 < baseStart_5723993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5723993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724057 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 1, 4, 2]
def baseStart_5724057 : Nat := 118140960795 + 5724057 * 2 ^ 59
def prefixEnd_5724057 : Nat := 4983230072969 + 3 ^ 40 * 5724057 * 2
def baseEnd_5724057 : Nat := 2939192534733016334363047

theorem tailTrace_5724057 : CollatzResearch.WordTrace tailWord_5724057 prefixEnd_5724057 2939192534733016334363047 := by
  unfold tailWord_5724057
  simp only [CollatzResearch.WordTrace]
  refine ⟨208773510223726554950706425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139182340149151036633804283 208773510223726554950706425)
  ·
    refine ⟨156580132667794916213029819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208773510223726554950706425 156580132667794916213029819)
    ·
      refine ⟨234870199001692374319544729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156580132667794916213029819 234870199001692374319544729)
      ·
        refine ⟨176152649251269280739658547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234870199001692374319544729 176152649251269280739658547)
        ·
          refine ⟨264228973876903921109487821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176152649251269280739658547 264228973876903921109487821)
          ·
            refine ⟨99085865203838970416057933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264228973876903921109487821 99085865203838970416057933)
            ·
              refine ⟨37157199451439613906021725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99085865203838970416057933 37157199451439613906021725)
              ·
                refine ⟨13933949794289855214758147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37157199451439613906021725 13933949794289855214758147)
                ·
                  refine ⟨20900924691434782822137221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13933949794289855214758147 20900924691434782822137221)
                  ·
                    refine ⟨3918923379644021779150729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20900924691434782822137221 3918923379644021779150729)
                    ·
                      refine ⟨2939192534733016334363047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918923379644021779150729 2939192534733016334363047)
                      ·
                        rfl

theorem cell23_5724057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_5724057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724057 prefixEnd_5724057 := by exact prefixLift 5724057
  have htrace : WordTrace (prefixWord ++ tailWord_5724057) baseStart_5724057 baseEnd_5724057 := by
    simpa [prefixWord, tailWord_5724057, baseEnd_5724057] using wordTrace_append hprefix tailTrace_5724057
  have hstable : (prefixWord ++ tailWord_5724057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724057).length < 2 ^ (prefixWord ++ tailWord_5724057).sum := by decide
  have hdescent : baseEnd_5724057 < baseStart_5724057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724108 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5724108 : Nat := 118140960795 + 5724108 * 2 ^ 59
def prefixEnd_5724108 : Nat := 4983230072969 + 3 ^ 40 * 5724108 * 2
def baseEnd_5724108 : Nat := 2939218722246395634825313

theorem tailTrace_5724108 : CollatzResearch.WordTrace tailWord_5724108 prefixEnd_5724108 2939218722246395634825313 := by
  unfold tailWord_5724108
  simp only [CollatzResearch.WordTrace]
  refine ⟨104387685173270895330406489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139183580231027860440541985 104387685173270895330406489)
  ·
    refine ⟨78290763879953171497804867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104387685173270895330406489 78290763879953171497804867)
    ·
      refine ⟨117436145819929757246707301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78290763879953171497804867 117436145819929757246707301)
      ·
        refine ⟨22019277341236829483757619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117436145819929757246707301 22019277341236829483757619)
        ·
          refine ⟨33028916011855244225636429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22019277341236829483757619 33028916011855244225636429)
          ·
            refine ⟨12385843504445716584613661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33028916011855244225636429 12385843504445716584613661)
            ·
              refine ⟨4644691314167143719230123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12385843504445716584613661 4644691314167143719230123)
              ·
                refine ⟨6967036971250715578845185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644691314167143719230123 6967036971250715578845185)
                ·
                  refine ⟨5225277728438036684133889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6967036971250715578845185 5225277728438036684133889)
                  ·
                    refine ⟨3918958296328527513100417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225277728438036684133889 3918958296328527513100417)
                    ·
                      refine ⟨2939218722246395634825313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918958296328527513100417 2939218722246395634825313)
                      ·
                        rfl

theorem cell23_5724108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5724108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724108 prefixEnd_5724108 := by exact prefixLift 5724108
  have htrace : WordTrace (prefixWord ++ tailWord_5724108) baseStart_5724108 baseEnd_5724108 := by
    simpa [prefixWord, tailWord_5724108, baseEnd_5724108] using wordTrace_append hprefix tailTrace_5724108
  have hstable : (prefixWord ++ tailWord_5724108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724108).length < 2 ^ (prefixWord ++ tailWord_5724108).sum := by decide
  have hdescent : baseEnd_5724108 < baseStart_5724108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724110 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_5724110 : Nat := 118140960795 + 5724110 * 2 ^ 59
def prefixEnd_5724110 : Nat := 4983230072969 + 3 ^ 40 * 5724110 * 2
def baseEnd_5724110 : Nat := 979739916402568209000101

theorem tailTrace_5724110 : CollatzResearch.WordTrace tailWord_5724110 prefixEnd_5724110 979739916402568209000101 := by
  unfold tailWord_5724110
  simp only [CollatzResearch.WordTrace]
  refine ⟨26096930411566818125298223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139183628861689696668257189 26096930411566818125298223)
  ·
    refine ⟨39145395617350227187947335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26096930411566818125298223 39145395617350227187947335)
    ·
      refine ⟨58718093426025340781921003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39145395617350227187947335 58718093426025340781921003)
      ·
        refine ⟨88077140139038011172881505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58718093426025340781921003 88077140139038011172881505)
        ·
          refine ⟨66057855104278508379661129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88077140139038011172881505 66057855104278508379661129)
          ·
            refine ⟨49543391328208881284745847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66057855104278508379661129 49543391328208881284745847)
            ·
              refine ⟨74315086992313321927118771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49543391328208881284745847 74315086992313321927118771)
              ·
                refine ⟨111472630488469982890678157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74315086992313321927118771 111472630488469982890678157)
                ·
                  refine ⟨41802236433176243584004309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111472630488469982890678157 41802236433176243584004309)
                  ·
                    refine ⟨979739916402568209000101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41802236433176243584004309 979739916402568209000101)
                    ·
                      rfl

theorem cell23_5724110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_5724110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724110 prefixEnd_5724110 := by exact prefixLift 5724110
  have htrace : WordTrace (prefixWord ++ tailWord_5724110) baseStart_5724110 baseEnd_5724110 := by
    simpa [prefixWord, tailWord_5724110, baseEnd_5724110] using wordTrace_append hprefix tailTrace_5724110
  have hstable : (prefixWord ++ tailWord_5724110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724110).length < 2 ^ (prefixWord ++ tailWord_5724110).sum := by decide
  have hdescent : baseEnd_5724110 < baseStart_5724110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724147 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 4, 4, 2]
def baseStart_5724147 : Nat := 118140960795 + 5724147 * 2 ^ 59
def prefixEnd_5724147 : Nat := 4983230072969 + 3 ^ 40 * 5724147 * 2
def baseEnd_5724147 : Nat := 2939238747991920982237633

theorem tailTrace_5724147 : CollatzResearch.WordTrace tailWord_5724147 prefixEnd_5724147 2939238747991920982237633 := by
  unfold tailWord_5724147
  simp only [CollatzResearch.WordTrace]
  refine ⟨208776792793400500321482695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139184528528933666880988463 208776792793400500321482695)
  ·
    refine ⟨313165189190100750482224043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208776792793400500321482695 313165189190100750482224043)
    ·
      refine ⟨469747783785151125723336065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313165189190100750482224043 469747783785151125723336065)
      ·
        refine ⟨352310837838863344292502049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469747783785151125723336065 352310837838863344292502049)
        ·
          refine ⟨264233128379147508219376537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352310837838863344292502049 264233128379147508219376537)
          ·
            refine ⟨198174846284360631164532403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264233128379147508219376537 198174846284360631164532403)
            ·
              refine ⟨297262269426540946746798605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198174846284360631164532403 297262269426540946746798605)
              ·
                refine ⟨111473351034952855030049477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297262269426540946746798605 111473351034952855030049477)
                ·
                  refine ⟨20901253319053660318134277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111473351034952855030049477 20901253319053660318134277)
                  ·
                    refine ⟨3918984997322561309650177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20901253319053660318134277 3918984997322561309650177)
                    ·
                      refine ⟨2939238747991920982237633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3918984997322561309650177 2939238747991920982237633)
                      ·
                        rfl

theorem cell23_5724147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4, 2].length) (baseStart_5724147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724147 prefixEnd_5724147 := by exact prefixLift 5724147
  have htrace : WordTrace (prefixWord ++ tailWord_5724147) baseStart_5724147 baseEnd_5724147 := by
    simpa [prefixWord, tailWord_5724147, baseEnd_5724147] using wordTrace_append hprefix tailTrace_5724147
  have hstable : (prefixWord ++ tailWord_5724147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724147).length < 2 ^ (prefixWord ++ tailWord_5724147).sum := by decide
  have hdescent : baseEnd_5724147 < baseStart_5724147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724160 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_5724160 : Nat := 118140960795 + 5724160 * 2 ^ 59
def prefixEnd_5724160 : Nat := 4983230072969 + 3 ^ 40 * 5724160 * 2
def baseEnd_5724160 : Nat := 2939245423240429431375073

theorem tailTrace_5724160 : CollatzResearch.WordTrace tailWord_5724160 prefixEnd_5724160 2939245423240429431375073 := by
  unfold tailWord_5724160
  simp only [CollatzResearch.WordTrace]
  refine ⟨104388633471176701770852967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139184844628235602361137289 104388633471176701770852967)
  ·
    refine ⟨156582950206765052656279451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104388633471176701770852967 156582950206765052656279451)
    ·
      refine ⟨234874425310147578984419177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156582950206765052656279451 234874425310147578984419177)
      ·
        refine ⟨176155818982610684238314383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234874425310147578984419177 176155818982610684238314383)
        ·
          refine ⟨264233728473916026357471575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176155818982610684238314383 264233728473916026357471575)
          ·
            refine ⟨396350592710874039536207363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264233728473916026357471575 396350592710874039536207363)
            ·
              refine ⟨594525889066311059304311045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396350592710874039536207363 594525889066311059304311045)
              ·
                refine ⟨111473604199933323619558321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594525889066311059304311045 111473604199933323619558321)
                ·
                  refine ⟨83605203149949992714668741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111473604199933323619558321 83605203149949992714668741)
                  ·
                    refine ⟨15675975590615623634000389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83605203149949992714668741 15675975590615623634000389)
                    ·
                      refine ⟨2939245423240429431375073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15675975590615623634000389 2939245423240429431375073)
                      ·
                        rfl

theorem cell23_5724160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_5724160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724160 prefixEnd_5724160 := by exact prefixLift 5724160
  have htrace : WordTrace (prefixWord ++ tailWord_5724160) baseStart_5724160 baseEnd_5724160 := by
    simpa [prefixWord, tailWord_5724160, baseEnd_5724160] using wordTrace_append hprefix tailTrace_5724160
  have hstable : (prefixWord ++ tailWord_5724160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724160).length < 2 ^ (prefixWord ++ tailWord_5724160).sum := by decide
  have hdescent : baseEnd_5724160 < baseStart_5724160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724184 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_5724184 : Nat := 118140960795 + 5724184 * 2 ^ 59
def prefixEnd_5724184 : Nat := 4983230072969 + 3 ^ 40 * 5724184 * 2
def baseEnd_5724184 : Nat := 2939257746776137337474963

theorem tailTrace_5724184 : CollatzResearch.WordTrace tailWord_5724184 prefixEnd_5724184 2939257746776137337474963 := by
  unfold tailWord_5724184
  simp only [CollatzResearch.WordTrace]
  refine ⟨104389071147133227820289803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139185428196177637093719737 104389071147133227820289803)
  ·
    refine ⟨156583606720699841730434705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104389071147133227820289803 156583606720699841730434705)
    ·
      refine ⟨117437705040524881297826029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156583606720699841730434705 117437705040524881297826029)
      ·
        refine ⟨44039139390196830486684761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117437705040524881297826029 44039139390196830486684761)
        ·
          refine ⟨33029354542647622865013571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44039139390196830486684761 33029354542647622865013571)
          ·
            refine ⟨49544031813971434297520357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33029354542647622865013571 49544031813971434297520357)
            ·
              refine ⟨9289505965119643930785067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49544031813971434297520357 9289505965119643930785067)
              ·
                refine ⟨13934258947679465896177601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9289505965119643930785067 13934258947679465896177601)
                ·
                  refine ⟨10450694210759599422133201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13934258947679465896177601 10450694210759599422133201)
                  ·
                    refine ⟨7838020658069699566599901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10450694210759599422133201 7838020658069699566599901)
                    ·
                      refine ⟨2939257746776137337474963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838020658069699566599901 2939257746776137337474963)
                      ·
                        rfl

theorem cell23_5724184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_5724184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724184 prefixEnd_5724184 := by exact prefixLift 5724184
  have htrace : WordTrace (prefixWord ++ tailWord_5724184) baseStart_5724184 baseEnd_5724184 := by
    simpa [prefixWord, tailWord_5724184, baseEnd_5724184] using wordTrace_append hprefix tailTrace_5724184
  have hstable : (prefixWord ++ tailWord_5724184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724184).length < 2 ^ (prefixWord ++ tailWord_5724184).sum := by decide
  have hdescent : baseEnd_5724184 < baseStart_5724184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724208 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 1, 4]
def baseStart_5724208 : Nat := 118140960795 + 5724208 * 2 ^ 59
def prefixEnd_5724208 : Nat := 4983230072969 + 3 ^ 40 * 5724208 * 2
def baseEnd_5724208 : Nat := 979756690103948414524951

theorem tailTrace_5724208 : CollatzResearch.WordTrace tailWord_5724208 prefixEnd_5724208 979756690103948414524951 := by
  unfold tailWord_5724208
  simp only [CollatzResearch.WordTrace]
  refine ⟨104389508823089753869726639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139186011764119671826302185 104389508823089753869726639)
  ·
    refine ⟨156584263234634630804589959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104389508823089753869726639 156584263234634630804589959)
    ·
      refine ⟨234876394851951946206884939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156584263234634630804589959 234876394851951946206884939)
      ·
        refine ⟨352314592277927919310327409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234876394851951946206884939 352314592277927919310327409)
        ·
          refine ⟨264235944208445939482745557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352314592277927919310327409 264235944208445939482745557)
          ·
            refine ⟨6193029942385451706626849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 264235944208445939482745557 6193029942385451706626849)
            ·
              refine ⟨4644772456789088779970137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193029942385451706626849 4644772456789088779970137)
              ·
                refine ⟨3483579342591816584977603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4644772456789088779970137 3483579342591816584977603)
                ·
                  refine ⟨5225369013887724877466405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483579342591816584977603 5225369013887724877466405)
                  ·
                    refine ⟨979756690103948414524951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225369013887724877466405 979756690103948414524951)
                    ·
                      rfl

theorem cell23_5724208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 4].length) (baseStart_5724208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724208 prefixEnd_5724208 := by exact prefixLift 5724208
  have htrace : WordTrace (prefixWord ++ tailWord_5724208) baseStart_5724208 baseEnd_5724208 := by
    simpa [prefixWord, tailWord_5724208, baseEnd_5724208] using wordTrace_append hprefix tailTrace_5724208
  have hstable : (prefixWord ++ tailWord_5724208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724208).length < 2 ^ (prefixWord ++ tailWord_5724208).sum := by decide
  have hdescent : baseEnd_5724208 < baseStart_5724208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724247 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 1, 6]
def baseStart_5724247 : Nat := 118140960795 + 5724247 * 2 ^ 59
def prefixEnd_5724247 : Nat := 4983230072969 + 3 ^ 40 * 5724247 * 2
def baseEnd_5724247 : Nat := 979763365352456863662391

theorem tailTrace_5724247 : CollatzResearch.WordTrace tailWord_5724247 prefixEnd_5724247 979763365352456863662391 := by
  unfold tailWord_5724247
  simp only [CollatzResearch.WordTrace]
  refine ⟨208780440093038217400122995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139186960062025478266748663 208780440093038217400122995)
  ·
    refine ⟨313170660139557326100184493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208780440093038217400122995 313170660139557326100184493)
    ·
      refine ⟨117438997552333997287569185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313170660139557326100184493 117438997552333997287569185)
      ·
        refine ⟨88079248164250497965676889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117438997552333997287569185 88079248164250497965676889)
        ·
          refine ⟨66059436123187873474257667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88079248164250497965676889 66059436123187873474257667)
          ·
            refine ⟨99089154184781810211386501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66059436123187873474257667 99089154184781810211386501)
            ·
              refine ⟨18579216409646589414634969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99089154184781810211386501 18579216409646589414634969)
              ·
                refine ⟨13934412307234942060976227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18579216409646589414634969 13934412307234942060976227)
                ·
                  refine ⟨20901618460852413091464341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13934412307234942060976227 20901618460852413091464341)
                  ·
                    refine ⟨979763365352456863662391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20901618460852413091464341 979763365352456863662391)
                    ·
                      rfl

theorem cell23_5724247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_5724247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724247 prefixEnd_5724247 := by exact prefixLift 5724247
  have htrace : WordTrace (prefixWord ++ tailWord_5724247) baseStart_5724247 baseEnd_5724247 := by
    simpa [prefixWord, tailWord_5724247, baseEnd_5724247] using wordTrace_append hprefix tailTrace_5724247
  have hstable : (prefixWord ++ tailWord_5724247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724247).length < 2 ^ (prefixWord ++ tailWord_5724247).sum := by decide
  have hdescent : baseEnd_5724247 < baseStart_5724247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724248 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 1, 1, 3]
def baseStart_5724248 : Nat := 118140960795 + 5724248 * 2 ^ 59
def prefixEnd_5724248 : Nat := 4983230072969 + 3 ^ 40 * 5724248 * 2
def baseEnd_5724248 : Nat := 2939290609538025087074669

theorem tailTrace_5724248 : CollatzResearch.WordTrace tailWord_5724248 prefixEnd_5724248 2939290609538025087074669 := by
  unfold tailWord_5724248
  simp only [CollatzResearch.WordTrace]
  refine ⟨104390238283017297285454699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139186984377356396380606265 104390238283017297285454699)
  ·
    refine ⟨156585357424525945928182049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104390238283017297285454699 156585357424525945928182049)
    ·
      refine ⟨117439018068394459446136537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156585357424525945928182049 117439018068394459446136537)
      ·
        refine ⟨88079263551295844584602403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117439018068394459446136537 88079263551295844584602403)
        ·
          refine ⟨132118895326943766876903605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88079263551295844584602403 132118895326943766876903605)
          ·
            refine ⟨12386146436900978144709713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132118895326943766876903605 12386146436900978144709713)
            ·
              refine ⟨9289609827675733608532285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12386146436900978144709713 9289609827675733608532285)
              ·
                refine ⟨3483603685378400103199607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9289609827675733608532285 3483603685378400103199607)
                ·
                  refine ⟨5225405528067600154799411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483603685378400103199607 5225405528067600154799411)
                  ·
                    refine ⟨7838108292101400232199117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225405528067600154799411 7838108292101400232199117)
                    ·
                      refine ⟨2939290609538025087074669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838108292101400232199117 2939290609538025087074669)
                      ·
                        rfl

theorem cell23_5724248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_5724248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724248 prefixEnd_5724248 := by exact prefixLift 5724248
  have htrace : WordTrace (prefixWord ++ tailWord_5724248) baseStart_5724248 baseEnd_5724248 := by
    simpa [prefixWord, tailWord_5724248, baseEnd_5724248] using wordTrace_append hprefix tailTrace_5724248
  have hstable : (prefixWord ++ tailWord_5724248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724248).length < 2 ^ (prefixWord ++ tailWord_5724248).sum := by decide
  have hdescent : baseEnd_5724248 < baseStart_5724248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724257 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_5724257 : Nat := 118140960795 + 5724257 * 2 ^ 59
def prefixEnd_5724257 : Nat := 4983230072969 + 3 ^ 40 * 5724257 * 2
def baseEnd_5724257 : Nat := 2939295230863915551862127

theorem tailTrace_5724257 : CollatzResearch.WordTrace tailWord_5724257 prefixEnd_5724257 2939295230863915551862127 := by
  unfold tailWord_5724257
  simp only [CollatzResearch.WordTrace]
  refine ⟨208780804823001989107987025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139187203215334659405324683 208780804823001989107987025)
  ·
    refine ⟨156585603617251491830990269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208780804823001989107987025 156585603617251491830990269)
    ·
      refine ⟨58719601356469309436621351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156585603617251491830990269 58719601356469309436621351)
      ·
        refine ⟨88079402034703964154932027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58719601356469309436621351 88079402034703964154932027)
        ·
          refine ⟨132119103052055946232398041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88079402034703964154932027 132119103052055946232398041)
          ·
            refine ⟨99089327289041959674298531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132119103052055946232398041 99089327289041959674298531)
            ·
              refine ⟨148633990933562939511447797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99089327289041959674298531 148633990933562939511447797)
              ·
                refine ⟨13934436650021525579198231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148633990933562939511447797 13934436650021525579198231)
                ·
                  refine ⟨20901654975032288368797347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13934436650021525579198231 20901654975032288368797347)
                  ·
                    refine ⟨31352482462548432553196021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20901654975032288368797347 31352482462548432553196021)
                    ·
                      refine ⟨2939295230863915551862127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31352482462548432553196021 2939295230863915551862127)
                      ·
                        rfl

theorem cell23_5724257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_5724257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724257 prefixEnd_5724257 := by exact prefixLift 5724257
  have htrace : WordTrace (prefixWord ++ tailWord_5724257) baseStart_5724257 baseEnd_5724257 := by
    simpa [prefixWord, tailWord_5724257, baseEnd_5724257] using wordTrace_append hprefix tailTrace_5724257
  have hstable : (prefixWord ++ tailWord_5724257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724257).length < 2 ^ (prefixWord ++ tailWord_5724257).sum := by decide
  have hdescent : baseEnd_5724257 < baseStart_5724257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724271 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 3, 2, 2]
def baseStart_5724271 : Nat := 118140960795 + 5724271 * 2 ^ 59
def prefixEnd_5724271 : Nat := 4983230072969 + 3 ^ 40 * 5724271 * 2
def baseEnd_5724271 : Nat := 2939302419593078497087063

theorem tailTrace_5724271 : CollatzResearch.WordTrace tailWord_5724271 prefixEnd_5724271 2939302419593078497087063 := by
  unfold tailWord_5724271
  simp only [CollatzResearch.WordTrace]
  refine ⟨208781315444951269498996667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139187543629967512999331111 208781315444951269498996667)
  ·
    refine ⟨313171973167426904248495001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208781315444951269498996667 313171973167426904248495001)
    ·
      refine ⟨234878979875570178186371251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313171973167426904248495001 234878979875570178186371251)
      ·
        refine ⟨352318469813355267279556877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234878979875570178186371251 352318469813355267279556877)
        ·
          refine ⟨132119426180008225229833829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352318469813355267279556877 132119426180008225229833829)
          ·
            refine ⟨24772392408751542230593843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132119426180008225229833829 24772392408751542230593843)
            ·
              refine ⟨37158588613127313345890765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24772392408751542230593843 37158588613127313345890765)
              ·
                refine ⟨13934470729922742504709037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37158588613127313345890765 13934470729922742504709037)
                ·
                  refine ⟨5225426523721028439265889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13934470729922742504709037 5225426523721028439265889)
                  ·
                    refine ⟨3919069892790771329449417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225426523721028439265889 3919069892790771329449417)
                    ·
                      refine ⟨2939302419593078497087063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919069892790771329449417 2939302419593078497087063)
                      ·
                        rfl

theorem cell23_5724271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 2, 2].length) (baseStart_5724271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724271 prefixEnd_5724271 := by exact prefixLift 5724271
  have htrace : WordTrace (prefixWord ++ tailWord_5724271) baseStart_5724271 baseEnd_5724271 := by
    simpa [prefixWord, tailWord_5724271, baseEnd_5724271] using wordTrace_append hprefix tailTrace_5724271
  have hstable : (prefixWord ++ tailWord_5724271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724271).length < 2 ^ (prefixWord ++ tailWord_5724271).sum := by decide
  have hdescent : baseEnd_5724271 < baseStart_5724271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724274 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5724274 : Nat := 118140960795 + 5724274 * 2 ^ 59
def prefixEnd_5724274 : Nat := 4983230072969 + 3 ^ 40 * 5724274 * 2
def baseEnd_5724274 : Nat := 2939303960035041985349549

theorem tailTrace_5724274 : CollatzResearch.WordTrace tailWord_5724274 prefixEnd_5724274 2939303960035041985349549 := by
  unfold tailWord_5724274
  simp only [CollatzResearch.WordTrace]
  refine ⟨52195356215985100252838969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139187616575960267340903917 52195356215985100252838969)
  ·
    refine ⟨39146517161988825189629227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52195356215985100252838969 39146517161988825189629227)
    ·
      refine ⟨58719775742983237784443841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39146517161988825189629227 58719775742983237784443841)
      ·
        refine ⟨44039831807237428338332881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58719775742983237784443841 44039831807237428338332881)
        ·
          refine ⟨33029873855428071253749661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44039831807237428338332881 33029873855428071253749661)
          ·
            refine ⟨12386202695785526720156123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33029873855428071253749661 12386202695785526720156123)
            ·
              refine ⟨18579304043678290080234185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12386202695785526720156123 18579304043678290080234185)
              ·
                refine ⟨13934478032758717560175639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18579304043678290080234185 13934478032758717560175639)
                ·
                  refine ⟨20901717049138076340263459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13934478032758717560175639 20901717049138076340263459)
                  ·
                    refine ⟨31352575573707114510395189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20901717049138076340263459 31352575573707114510395189)
                    ·
                      refine ⟨2939303960035041985349549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31352575573707114510395189 2939303960035041985349549)
                      ·
                        rfl

theorem cell23_5724274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5724274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724274 prefixEnd_5724274 := by exact prefixLift 5724274
  have htrace : WordTrace (prefixWord ++ tailWord_5724274) baseStart_5724274 baseEnd_5724274 := by
    simpa [prefixWord, tailWord_5724274, baseEnd_5724274] using wordTrace_append hprefix tailTrace_5724274
  have hstable : (prefixWord ++ tailWord_5724274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724274).length < 2 ^ (prefixWord ++ tailWord_5724274).sum := by decide
  have hdescent : baseEnd_5724274 < baseStart_5724274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724284 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_5724284 : Nat := 118140960795 + 5724284 * 2 ^ 59
def prefixEnd_5724284 : Nat := 4983230072969 + 3 ^ 40 * 5724284 * 2
def baseEnd_5724284 : Nat := 2939309094841586946224503

theorem tailTrace_5724284 : CollatzResearch.WordTrace tailWord_5724284 prefixEnd_5724284 2939309094841586946224503 := by
  unfold tailWord_5724284
  simp only [CollatzResearch.WordTrace]
  refine ⟨104390894796952086359609953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139187859729269448479479937 104390894796952086359609953)
  ·
    refine ⟨78293171097714064769707465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104390894796952086359609953 78293171097714064769707465)
    ·
      refine ⟨58719878323285548577280599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78293171097714064769707465 58719878323285548577280599)
      ·
        refine ⟨88079817484928322865920899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58719878323285548577280599 88079817484928322865920899)
        ·
          refine ⟨132119726227392484298881349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88079817484928322865920899 132119726227392484298881349)
          ·
            refine ⟨24772448667636090806040253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132119726227392484298881349 24772448667636090806040253)
            ·
              refine ⟨9289668250363534052265095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24772448667636090806040253 9289668250363534052265095)
              ·
                refine ⟨13934502375545301078397643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9289668250363534052265095 13934502375545301078397643)
                ·
                  refine ⟨20901753563317951617596465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13934502375545301078397643 20901753563317951617596465)
                  ·
                    refine ⟨15676315172488463713197349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20901753563317951617596465 15676315172488463713197349)
                    ·
                      refine ⟨2939309094841586946224503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15676315172488463713197349 2939309094841586946224503)
                      ·
                        rfl

theorem cell23_5724284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_5724284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724284 prefixEnd_5724284 := by exact prefixLift 5724284
  have htrace : WordTrace (prefixWord ++ tailWord_5724284) baseStart_5724284 baseEnd_5724284 := by
    simpa [prefixWord, tailWord_5724284, baseEnd_5724284] using wordTrace_append hprefix tailTrace_5724284
  have hstable : (prefixWord ++ tailWord_5724284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724284).length < 2 ^ (prefixWord ++ tailWord_5724284).sum := by decide
  have hdescent : baseEnd_5724284 < baseStart_5724284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724291 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 3]
def baseStart_5724291 : Nat := 118140960795 + 5724291 * 2 ^ 59
def prefixEnd_5724291 : Nat := 4983230072969 + 3 ^ 40 * 5724291 * 2
def baseEnd_5724291 : Nat := 2939312689206168418836971

theorem tailTrace_5724291 : CollatzResearch.WordTrace tailWord_5724291 prefixEnd_5724291 2939312689206168418836971 := by
  unfold tailWord_5724291
  simp only [CollatzResearch.WordTrace]
  refine ⟨208782044904878812914724727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139188029936585875276483151 208782044904878812914724727)
  ·
    refine ⟨313173067357318219372087091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208782044904878812914724727 313173067357318219372087091)
    ·
      refine ⟨469759601035977329058130637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313173067357318219372087091 469759601035977329058130637)
      ·
        refine ⟨176159850388491498396798989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469759601035977329058130637 176159850388491498396798989)
        ·
          refine ⟨66059943895684311898799621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176159850388491498396798989 66059943895684311898799621)
          ·
            refine ⟨12386239480440808481024929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66059943895684311898799621 12386239480440808481024929)
            ·
              refine ⟨9289679610330606360768697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12386239480440808481024929 9289679610330606360768697)
              ·
                refine ⟨6967259707747954770576523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9289679610330606360768697 6967259707747954770576523)
                ·
                  refine ⟨10450889561621932155864785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6967259707747954770576523 10450889561621932155864785)
                  ·
                    refine ⟨7838167171216449116898589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10450889561621932155864785 7838167171216449116898589)
                    ·
                      refine ⟨2939312689206168418836971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838167171216449116898589 2939312689206168418836971)
                      ·
                        rfl

theorem cell23_5724291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_5724291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724291 prefixEnd_5724291 := by exact prefixLift 5724291
  have htrace : WordTrace (prefixWord ++ tailWord_5724291) baseStart_5724291 baseEnd_5724291 := by
    simpa [prefixWord, tailWord_5724291, baseEnd_5724291] using wordTrace_append hprefix tailTrace_5724291
  have hstable : (prefixWord ++ tailWord_5724291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724291).length < 2 ^ (prefixWord ++ tailWord_5724291).sum := by decide
  have hdescent : baseEnd_5724291 < baseStart_5724291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724304 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 6, 1, 3]
def baseStart_5724304 : Nat := 118140960795 + 5724304 * 2 ^ 59
def prefixEnd_5724304 : Nat := 4983230072969 + 3 ^ 40 * 5724304 * 2
def baseEnd_5724304 : Nat := 2939319364454676867974411

theorem tailTrace_5724304 : CollatzResearch.WordTrace tailWord_5724304 prefixEnd_5724304 2939319364454676867974411 := by
  unfold tailWord_5724304
  simp only [CollatzResearch.WordTrace]
  refine ⟨104391259526915858067473983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139188346035887810756631977 104391259526915858067473983)
  ·
    refine ⟨156586889290373787101210975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104391259526915858067473983 156586889290373787101210975)
    ·
      refine ⟨234880333935560680651816463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156586889290373787101210975 234880333935560680651816463)
      ·
        refine ⟨352320500903341020977724695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234880333935560680651816463 352320500903341020977724695)
        ·
          refine ⟨528480751355011531466587043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352320500903341020977724695 528480751355011531466587043)
          ·
            refine ⟨792721127032517297199880565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528480751355011531466587043 792721127032517297199880565)
            ·
              refine ⟨74317605659298496612488803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 792721127032517297199880565 74317605659298496612488803)
              ·
                refine ⟨111476408488947744918733205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74317605659298496612488803 111476408488947744918733205)
                ·
                  refine ⟨5225456647919425543065619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111476408488947744918733205 5225456647919425543065619)
                  ·
                    refine ⟨7838184971879138314598429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225456647919425543065619 7838184971879138314598429)
                    ·
                      refine ⟨2939319364454676867974411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838184971879138314598429 2939319364454676867974411)
                      ·
                        rfl

theorem cell23_5724304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_5724304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724304 prefixEnd_5724304 := by exact prefixLift 5724304
  have htrace : WordTrace (prefixWord ++ tailWord_5724304) baseStart_5724304 baseEnd_5724304 := by
    simpa [prefixWord, tailWord_5724304, baseEnd_5724304] using wordTrace_append hprefix tailTrace_5724304
  have hstable : (prefixWord ++ tailWord_5724304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724304).length < 2 ^ (prefixWord ++ tailWord_5724304).sum := by decide
  have hdescent : baseEnd_5724304 < baseStart_5724304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724308 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5724308 : Nat := 118140960795 + 5724308 * 2 ^ 59
def prefixEnd_5724308 : Nat := 4983230072969 + 3 ^ 40 * 5724308 * 2
def baseEnd_5724308 : Nat := 2939321418377294852324393

theorem tailTrace_5724308 : CollatzResearch.WordTrace tailWord_5724308 prefixEnd_5724308 2939321418377294852324393 := by
  unfold tailWord_5724308
  simp only [CollatzResearch.WordTrace]
  refine ⟨104391332472908612409046789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139188443297211483212062385 104391332472908612409046789)
  ·
    refine ⟨19573374838670364826696273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104391332472908612409046789 19573374838670364826696273)
    ·
      refine ⟨14680031129002773620022205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19573374838670364826696273 14680031129002773620022205)
      ·
        refine ⟨5505011673376040107508327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14680031129002773620022205 5505011673376040107508327)
        ·
          refine ⟨8257517510064060161262491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5505011673376040107508327 8257517510064060161262491)
          ·
            refine ⟨12386276265096090241893737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8257517510064060161262491 12386276265096090241893737)
            ·
              refine ⟨9289707198822067681420303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12386276265096090241893737 9289707198822067681420303)
              ·
                refine ⟨13934560798233101522130455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9289707198822067681420303 13934560798233101522130455)
                ·
                  refine ⟨20901841197349652283195683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13934560798233101522130455 20901841197349652283195683)
                  ·
                    refine ⟨31352761796024478424793525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20901841197349652283195683 31352761796024478424793525)
                    ·
                      refine ⟨2939321418377294852324393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31352761796024478424793525 2939321418377294852324393)
                      ·
                        rfl

theorem cell23_5724308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5724308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724308 prefixEnd_5724308 := by exact prefixLift 5724308
  have htrace : WordTrace (prefixWord ++ tailWord_5724308) baseStart_5724308 baseEnd_5724308 := by
    simpa [prefixWord, tailWord_5724308, baseEnd_5724308] using wordTrace_append hprefix tailTrace_5724308
  have hstable : (prefixWord ++ tailWord_5724308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724308).length < 2 ^ (prefixWord ++ tailWord_5724308).sum := by decide
  have hdescent : baseEnd_5724308 < baseStart_5724308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724321 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5724321 : Nat := 118140960795 + 5724321 * 2 ^ 59
def prefixEnd_5724321 : Nat := 4983230072969 + 3 ^ 40 * 5724321 * 2
def baseEnd_5724321 : Nat := 2939328093625803301461833

theorem tailTrace_5724321 : CollatzResearch.WordTrace tailWord_5724321 prefixEnd_5724321 2939328093625803301461833 := by
  unfold tailWord_5724321
  simp only [CollatzResearch.WordTrace]
  refine ⟨208783139094770128038316817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139188759396513418692211211 208783139094770128038316817)
  ·
    refine ⟨156587354321077596028737613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208783139094770128038316817 156587354321077596028737613)
    ·
      refine ⟨58720257870404098510776605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156587354321077596028737613 58720257870404098510776605)
      ·
        refine ⟨22020096701401536941541227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58720257870404098510776605 22020096701401536941541227)
        ·
          refine ⟨33030145052102305412311841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22020096701401536941541227 33030145052102305412311841)
          ·
            refine ⟨24772608789076729059233881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33030145052102305412311841 24772608789076729059233881)
            ·
              refine ⟨18579456591807546794425411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24772608789076729059233881 18579456591807546794425411)
              ·
                refine ⟨27869184887711320191638117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18579456591807546794425411 27869184887711320191638117)
                ·
                  refine ⟨5225472166445872535932147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27869184887711320191638117 5225472166445872535932147)
                  ·
                    refine ⟨7838208249668808803898221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5225472166445872535932147 7838208249668808803898221)
                    ·
                      refine ⟨2939328093625803301461833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838208249668808803898221 2939328093625803301461833)
                      ·
                        rfl

theorem cell23_5724321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5724321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724321 prefixEnd_5724321 := by exact prefixLift 5724321
  have htrace : WordTrace (prefixWord ++ tailWord_5724321) baseStart_5724321 baseEnd_5724321 := by
    simpa [prefixWord, tailWord_5724321, baseEnd_5724321] using wordTrace_append hprefix tailTrace_5724321
  have hstable : (prefixWord ++ tailWord_5724321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724321).length < 2 ^ (prefixWord ++ tailWord_5724321).sum := by decide
  have hdescent : baseEnd_5724321 < baseStart_5724321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724347 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5]
def baseStart_5724347 : Nat := 118140960795 + 5724347 * 2 ^ 59
def prefixEnd_5724347 : Nat := 4983230072969 + 3 ^ 40 * 5724347 * 2
def baseEnd_5724347 : Nat := 2939341444122820199736713

theorem tailTrace_5724347 : CollatzResearch.WordTrace tailWord_5724347 prefixEnd_5724347 2939341444122820199736713 := by
  unfold tailWord_5724347
  simp only [CollatzResearch.WordTrace]
  refine ⟨208784087392675934478763295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139189391595117289652508863 208784087392675934478763295)
  ·
    refine ⟨313176131089013901718144943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208784087392675934478763295 313176131089013901718144943)
    ·
      refine ⟨469764196633520852577217415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313176131089013901718144943 469764196633520852577217415)
      ·
        refine ⟨704646294950281278865826123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469764196633520852577217415 704646294950281278865826123)
        ·
          refine ⟨1056969442425421918298739185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704646294950281278865826123 1056969442425421918298739185)
          ·
            refine ⟨792727081819066438724054389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056969442425421918298739185 792727081819066438724054389)
            ·
              refine ⟨74318163920537478630380099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 792727081819066438724054389 74318163920537478630380099)
              ·
                refine ⟨111477245880806217945570149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74318163920537478630380099 111477245880806217945570149)
                ·
                  refine ⟨20901983602651165864794403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111477245880806217945570149 20901983602651165864794403)
                  ·
                    refine ⟨31352975403976748797191605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20901983602651165864794403 31352975403976748797191605)
                    ·
                      refine ⟨2939341444122820199736713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31352975403976748797191605 2939341444122820199736713)
                      ·
                        rfl

theorem cell23_5724347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_5724347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724347 prefixEnd_5724347 := by exact prefixLift 5724347
  have htrace : WordTrace (prefixWord ++ tailWord_5724347) baseStart_5724347 baseEnd_5724347 := by
    simpa [prefixWord, tailWord_5724347, baseEnd_5724347] using wordTrace_append hprefix tailTrace_5724347
  have hstable : (prefixWord ++ tailWord_5724347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724347).length < 2 ^ (prefixWord ++ tailWord_5724347).sum := by decide
  have hdescent : baseEnd_5724347 < baseStart_5724347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724348 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_5724348 : Nat := 118140960795 + 5724348 * 2 ^ 59
def prefixEnd_5724348 : Nat := 4983230072969 + 3 ^ 40 * 5724348 * 2
def baseEnd_5724348 : Nat := 2939341957603474695824209

theorem tailTrace_5724348 : CollatzResearch.WordTrace tailWord_5724348 prefixEnd_5724348 2939341957603474695824209 := by
  unfold tailWord_5724348
  simp only [CollatzResearch.WordTrace]
  refine ⟨104392061932836155824774849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139189415910448207766366465 104392061932836155824774849)
  ·
    refine ⟨78294046449627116868581137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104392061932836155824774849 78294046449627116868581137)
    ·
      refine ⟨58720534837220337651435853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78294046449627116868581137 58720534837220337651435853)
      ·
        refine ⟨22020200563957626619288445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58720534837220337651435853 22020200563957626619288445)
        ·
          refine ⟨8257575211484109982233167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22020200563957626619288445 8257575211484109982233167)
          ·
            refine ⟨12386362817226164973349751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8257575211484109982233167 12386362817226164973349751)
            ·
              refine ⟨18579544225839247460024627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12386362817226164973349751 18579544225839247460024627)
              ·
                refine ⟨27869316338758871190036941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18579544225839247460024627 27869316338758871190036941)
                ·
                  refine ⟨10450993627034576696263853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27869316338758871190036941 10450993627034576696263853)
                  ·
                    refine ⟨3919122610137966261098945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10450993627034576696263853 3919122610137966261098945)
                    ·
                      refine ⟨2939341957603474695824209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919122610137966261098945 2939341957603474695824209)
                      ·
                        rfl

theorem cell23_5724348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_5724348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724348 prefixEnd_5724348 := by exact prefixLift 5724348
  have htrace : WordTrace (prefixWord ++ tailWord_5724348) baseStart_5724348 baseEnd_5724348 := by
    simpa [prefixWord, tailWord_5724348, baseEnd_5724348] using wordTrace_append hprefix tailTrace_5724348
  have hstable : (prefixWord ++ tailWord_5724348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724348).length < 2 ^ (prefixWord ++ tailWord_5724348).sum := by decide
  have hdescent : baseEnd_5724348 < baseStart_5724348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724361 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 4, 2, 2]
def baseStart_5724361 : Nat := 118140960795 + 5724361 * 2 ^ 59
def prefixEnd_5724361 : Nat := 4983230072969 + 3 ^ 40 * 5724361 * 2
def baseEnd_5724361 : Nat := 2939348632851983144961649

theorem tailTrace_5724361 : CollatzResearch.WordTrace tailWord_5724361 prefixEnd_5724361 2939348632851983144961649 := by
  unfold tailWord_5724361
  simp only [CollatzResearch.WordTrace]
  refine ⟨208784598014625214869772937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139189732009750143246515291 208784598014625214869772937)
  ·
    refine ⟨156588448510968911152329703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208784598014625214869772937 156588448510968911152329703)
    ·
      refine ⟨234882672766453366728494555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156588448510968911152329703 234882672766453366728494555)
      ·
        refine ⟨352324009149680050092741833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234882672766453366728494555 352324009149680050092741833)
        ·
          refine ⟨264243006862260037569556375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352324009149680050092741833 264243006862260037569556375)
          ·
            refine ⟨396364510293390056354334563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264243006862260037569556375 396364510293390056354334563)
            ·
              refine ⟨594546765440085084531501845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396364510293390056354334563 594546765440085084531501845)
              ·
                refine ⟨27869379630003988337414149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 594546765440085084531501845 27869379630003988337414149)
                ·
                  refine ⟨5225508680625747813265153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27869379630003988337414149 5225508680625747813265153)
                  ·
                    refine ⟨3919131510469310859948865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225508680625747813265153 3919131510469310859948865)
                    ·
                      refine ⟨2939348632851983144961649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919131510469310859948865 2939348632851983144961649)
                      ·
                        rfl

theorem cell23_5724361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 2, 2].length) (baseStart_5724361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724361 prefixEnd_5724361 := by exact prefixLift 5724361
  have htrace : WordTrace (prefixWord ++ tailWord_5724361) baseStart_5724361 baseEnd_5724361 := by
    simpa [prefixWord, tailWord_5724361, baseEnd_5724361] using wordTrace_append hprefix tailTrace_5724361
  have hstable : (prefixWord ++ tailWord_5724361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724361).length < 2 ^ (prefixWord ++ tailWord_5724361).sum := by decide
  have hdescent : baseEnd_5724361 < baseStart_5724361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724377 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_5724377 : Nat := 118140960795 + 5724377 * 2 ^ 59
def prefixEnd_5724377 : Nat := 4983230072969 + 3 ^ 40 * 5724377 * 2
def baseEnd_5724377 : Nat := 2939356848542455082361575

theorem tailTrace_5724377 : CollatzResearch.WordTrace tailWord_5724377 prefixEnd_5724377 2939356848542455082361575 := by
  unfold tailWord_5724377
  simp only [CollatzResearch.WordTrace]
  refine ⟨208785181582567249602355385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139190121055044833068236923 208785181582567249602355385)
  ·
    refine ⟨156588886186925437201766539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208785181582567249602355385 156588886186925437201766539)
    ·
      refine ⟨234883329280388155802649809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156588886186925437201766539 234883329280388155802649809)
      ·
        refine ⟨176162496960291116851987357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234883329280388155802649809 176162496960291116851987357)
        ·
          refine ⟨66060936360109168819495259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176162496960291116851987357 66060936360109168819495259)
          ·
            refine ⟨99091404540163753229242889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66060936360109168819495259 99091404540163753229242889)
            ·
              refine ⟨74318553405122814921932167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99091404540163753229242889 74318553405122814921932167)
              ·
                refine ⟨111477830107684222382898251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74318553405122814921932167 111477830107684222382898251)
                ·
                  refine ⟨167216745161526333574347377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111477830107684222382898251 167216745161526333574347377)
                  ·
                    refine ⟨125412558871144750180760533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167216745161526333574347377 125412558871144750180760533)
                    ·
                      refine ⟨2939356848542455082361575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125412558871144750180760533 2939356848542455082361575)
                      ·
                        rfl

theorem cell23_5724377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_5724377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724377 prefixEnd_5724377 := by exact prefixLift 5724377
  have htrace : WordTrace (prefixWord ++ tailWord_5724377) baseStart_5724377 baseEnd_5724377 := by
    simpa [prefixWord, tailWord_5724377, baseEnd_5724377] using wordTrace_append hprefix tailTrace_5724377
  have hstable : (prefixWord ++ tailWord_5724377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724377).length < 2 ^ (prefixWord ++ tailWord_5724377).sum := by decide
  have hdescent : baseEnd_5724377 < baseStart_5724377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724378 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2]
def baseStart_5724378 : Nat := 118140960795 + 5724378 * 2 ^ 59
def prefixEnd_5724378 : Nat := 4983230072969 + 3 ^ 40 * 5724378 * 2
def baseEnd_5724378 : Nat := 2939357362023109578449071

theorem tailTrace_5724378 : CollatzResearch.WordTrace tailWord_5724378 prefixEnd_5724378 2939357362023109578449071 := by
  unfold tailWord_5724378
  simp only [CollatzResearch.WordTrace]
  refine ⟨52196304513890906693285447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139190145370375751182094525 52196304513890906693285447)
  ·
    refine ⟨78294456770836360039928171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52196304513890906693285447 78294456770836360039928171)
    ·
      refine ⟨117441685156254540059892257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78294456770836360039928171 117441685156254540059892257)
      ·
        refine ⟨88081263867190905044919193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117441685156254540059892257 88081263867190905044919193)
        ·
          refine ⟨66060947900393178783689395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88081263867190905044919193 66060947900393178783689395)
          ·
            refine ⟨99091421850589768175534093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66060947900393178783689395 99091421850589768175534093)
            ·
              refine ⟨37159283193971163065825285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99091421850589768175534093 37159283193971163065825285)
              ·
                refine ⟨6967365598869593074842241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37159283193971163065825285 6967365598869593074842241)
                ·
                  refine ⟨5225524199152194806131681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6967365598869593074842241 5225524199152194806131681)
                  ·
                    refine ⟨3919143149364146104598761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225524199152194806131681 3919143149364146104598761)
                    ·
                      refine ⟨2939357362023109578449071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919143149364146104598761 2939357362023109578449071)
                      ·
                        rfl

theorem cell23_5724378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_5724378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724378 prefixEnd_5724378 := by exact prefixLift 5724378
  have htrace : WordTrace (prefixWord ++ tailWord_5724378) baseStart_5724378 baseEnd_5724378 := by
    simpa [prefixWord, tailWord_5724378, baseEnd_5724378] using wordTrace_append hprefix tailTrace_5724378
  have hstable : (prefixWord ++ tailWord_5724378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724378).length < 2 ^ (prefixWord ++ tailWord_5724378).sum := by decide
  have hdescent : baseEnd_5724378 < baseStart_5724378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724381 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5724381 : Nat := 118140960795 + 5724381 * 2 ^ 59
def prefixEnd_5724381 : Nat := 4983230072969 + 3 ^ 40 * 5724381 * 2
def baseEnd_5724381 : Nat := 2939358902465073066711557

theorem tailTrace_5724381 : CollatzResearch.WordTrace tailWord_5724381 prefixEnd_5724381 2939358902465073066711557 := by
  unfold tailWord_5724381
  simp only [CollatzResearch.WordTrace]
  refine ⟨208785327474552758285500997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139190218316368505523667331 208785327474552758285500997)
  ·
    refine ⟨39147248901478642178531437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208785327474552758285500997 39147248901478642178531437)
    ·
      refine ⟨14680218338054490816949289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39147248901478642178531437 14680218338054490816949289)
      ·
        refine ⟨11010163753540868112711967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14680218338054490816949289 11010163753540868112711967)
        ·
          refine ⟨16515245630311302169067951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010163753540868112711967 16515245630311302169067951)
          ·
            refine ⟨24772868445466953253601927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16515245630311302169067951 24772868445466953253601927)
            ·
              refine ⟨37159302668200429880402891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24772868445466953253601927 37159302668200429880402891)
              ·
                refine ⟨55738954002300644820604337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37159302668200429880402891 55738954002300644820604337)
                ·
                  refine ⟨41804215501725483615453253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55738954002300644820604337 41804215501725483615453253)
                  ·
                    refine ⟨7838290406573528177897485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41804215501725483615453253 7838290406573528177897485)
                    ·
                      refine ⟨2939358902465073066711557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838290406573528177897485 2939358902465073066711557)
                      ·
                        rfl

theorem cell23_5724381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5724381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724381 prefixEnd_5724381 := by exact prefixLift 5724381
  have htrace : WordTrace (prefixWord ++ tailWord_5724381) baseStart_5724381 baseEnd_5724381 := by
    simpa [prefixWord, tailWord_5724381, baseEnd_5724381] using wordTrace_append hprefix tailTrace_5724381
  have hstable : (prefixWord ++ tailWord_5724381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724381).length < 2 ^ (prefixWord ++ tailWord_5724381).sum := by decide
  have hdescent : baseEnd_5724381 < baseStart_5724381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724391 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5724391 : Nat := 118140960795 + 5724391 * 2 ^ 59
def prefixEnd_5724391 : Nat := 4983230072969 + 3 ^ 40 * 5724391 * 2
def baseEnd_5724391 : Nat := 2939364037271618027586511

theorem tailTrace_5724391 : CollatzResearch.WordTrace tailWord_5724391 prefixEnd_5724391 2939364037271618027586511 := by
  unfold tailWord_5724391
  simp only [CollatzResearch.WordTrace]
  refine ⟨208785692204516529993365027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139190461469677686662243351 208785692204516529993365027)
  ·
    refine ⟨313178538306774794990047541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208785692204516529993365027 313178538306774794990047541)
    ·
      refine ⟨29360487966260137030316957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313178538306774794990047541 29360487966260137030316957)
      ·
        refine ⟨11010182987347551386368859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29360487966260137030316957 11010182987347551386368859)
        ·
          refine ⟨16515274481021327079553289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010182987347551386368859 16515274481021327079553289)
          ·
            refine ⟨12386455860765995309664967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16515274481021327079553289 12386455860765995309664967)
            ·
              refine ⟨18579683791148992964497451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12386455860765995309664967 18579683791148992964497451)
              ·
                refine ⟨27869525686723489446746177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18579683791148992964497451 27869525686723489446746177)
                ·
                  refine ⟨20902144265042617085059633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27869525686723489446746177 20902144265042617085059633)
                  ·
                    refine ⟨15676608198781962813794725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20902144265042617085059633 15676608198781962813794725)
                    ·
                      refine ⟨2939364037271618027586511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15676608198781962813794725 2939364037271618027586511)
                      ·
                        rfl

theorem cell23_5724391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5724391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724391 prefixEnd_5724391 := by exact prefixLift 5724391
  have htrace : WordTrace (prefixWord ++ tailWord_5724391) baseStart_5724391 baseEnd_5724391 := by
    simpa [prefixWord, tailWord_5724391, baseEnd_5724391] using wordTrace_append hprefix tailTrace_5724391
  have hstable : (prefixWord ++ tailWord_5724391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724391).length < 2 ^ (prefixWord ++ tailWord_5724391).sum := by decide
  have hdescent : baseEnd_5724391 < baseStart_5724391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724418 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_5724418 : Nat := 118140960795 + 5724418 * 2 ^ 59
def prefixEnd_5724418 : Nat := 4983230072969 + 3 ^ 40 * 5724418 * 2
def baseEnd_5724418 : Nat := 326597544583254380216543

theorem tailTrace_5724418 : CollatzResearch.WordTrace tailWord_5724418 prefixEnd_5724418 326597544583254380216543 := by
  unfold tailWord_5724418
  simp only [CollatzResearch.WordTrace]
  refine ⟨52196669243854678401149477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139191117983612475736398605 52196669243854678401149477)
  ·
    refine ⟨9786875483222752200215527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52196669243854678401149477 9786875483222752200215527)
    ·
      refine ⟨14680313224834128300323291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9786875483222752200215527 14680313224834128300323291)
      ·
        refine ⟨22020469837251192450484937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14680313224834128300323291 22020469837251192450484937)
        ·
          refine ⟨16515352377938394337863703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22020469837251192450484937 16515352377938394337863703)
          ·
            refine ⟨24773028566907591506795555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16515352377938394337863703 24773028566907591506795555)
            ·
              refine ⟨37159542850361387260193333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24773028566907591506795555 37159542850361387260193333)
              ·
                refine ⟨3483707142221380055643125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37159542850361387260193333 3483707142221380055643125)
                ·
                  refine ⟨326597544583254380216543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3483707142221380055643125 326597544583254380216543)
                  ·
                    rfl

theorem cell23_5724418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_5724418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724418 prefixEnd_5724418 := by exact prefixLift 5724418
  have htrace : WordTrace (prefixWord ++ tailWord_5724418) baseStart_5724418 baseEnd_5724418 := by
    simpa [prefixWord, tailWord_5724418, baseEnd_5724418] using wordTrace_append hprefix tailTrace_5724418
  have hstable : (prefixWord ++ tailWord_5724418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724418).length < 2 ^ (prefixWord ++ tailWord_5724418).sum := by decide
  have hdescent : baseEnd_5724418 < baseStart_5724418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724451 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 2, 4, 2]
def baseStart_5724451 : Nat := 118140960795 + 5724451 * 2 ^ 59
def prefixEnd_5724451 : Nat := 4983230072969 + 3 ^ 40 * 5724451 * 2
def baseEnd_5724451 : Nat := 2939394846110887792836235

theorem tailTrace_5724451 : CollatzResearch.WordTrace tailWord_5724451 prefixEnd_5724451 2939394846110887792836235 := by
  unfold tailWord_5724451
  simp only [CollatzResearch.WordTrace]
  refine ⟨208787880584299160240549207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139191920389532773493699471 208787880584299160240549207)
  ·
    refine ⟨313181820876448740360823811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208787880584299160240549207 313181820876448740360823811)
    ·
      refine ⟨469772731314673110541235717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313181820876448740360823811 469772731314673110541235717)
      ·
        refine ⟨88082387121501208226481697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469772731314673110541235717 88082387121501208226481697)
        ·
          refine ⟨66061790341125906169861273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88082387121501208226481697 66061790341125906169861273)
          ·
            refine ⟨49546342755844429627395955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66061790341125906169861273 49546342755844429627395955)
            ·
              refine ⟨74319514133766644441093933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49546342755844429627395955 74319514133766644441093933)
              ·
                refine ⟨27869817800162491665410225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74319514133766644441093933 27869817800162491665410225)
                ·
                  refine ⟨20902363350121868749057669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27869817800162491665410225 20902363350121868749057669)
                  ·
                    refine ⟨3919193128147850390448313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20902363350121868749057669 3919193128147850390448313)
                    ·
                      refine ⟨2939394846110887792836235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919193128147850390448313 2939394846110887792836235)
                      ·
                        rfl

theorem cell23_5724451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_5724451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724451 prefixEnd_5724451 := by exact prefixLift 5724451
  have htrace : WordTrace (prefixWord ++ tailWord_5724451) baseStart_5724451 baseEnd_5724451 := by
    simpa [prefixWord, tailWord_5724451, baseEnd_5724451] using wordTrace_append hprefix tailTrace_5724451
  have hstable : (prefixWord ++ tailWord_5724451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724451).length < 2 ^ (prefixWord ++ tailWord_5724451).sum := by decide
  have hdescent : baseEnd_5724451 < baseStart_5724451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
