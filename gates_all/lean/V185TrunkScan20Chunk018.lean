import V185TrunkScan20Chunk017

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_108783 : List Nat := [1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_108783 : Nat := 118140960795 + 108783 * 2 ^ 59
def prefixEnd_108783 : Nat := 4983230072969 + 3 ^ 40 * 108783 * 2
def baseEnd_108783 : Nat := 16550508455749072507325

theorem tailTrace_108783 : CollatzResearch.WordTrace tailWord_108783 prefixEnd_108783 16550508455749072507325 := by
  unfold tailWord_108783
  simp only [CollatzResearch.WordTrace]
  refine ⟨3967641964905244502387003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2645094643270163001591335 3967641964905244502387003)
  ·
    refine ⟨5951462947357866753580505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3967641964905244502387003 5951462947357866753580505)
    ·
      refine ⟨4463597210518400065185379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5951462947357866753580505 4463597210518400065185379)
      ·
        refine ⟨6695395815777600097778069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4463597210518400065185379 6695395815777600097778069)
        ·
          refine ⟨313846678864575004583347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6695395815777600097778069 313846678864575004583347)
          ·
            refine ⟨470770018296862506875021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313846678864575004583347 470770018296862506875021)
            ·
              refine ⟨176538756861323440078133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470770018296862506875021 176538756861323440078133)
              ·
                refine ⟨16550508455749072507325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176538756861323440078133 16550508455749072507325)
                ·
                  rfl

theorem cell20_108783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_108783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108783 prefixEnd_108783 := by exact prefixLift 108783
  have htrace : WordTrace (prefixWord ++ tailWord_108783) baseStart_108783 baseEnd_108783 := by
    simpa [prefixWord, tailWord_108783, baseEnd_108783] using wordTrace_append hprefix tailTrace_108783
  have hstable : (prefixWord ++ tailWord_108783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108783).length < 2 ^ (prefixWord ++ tailWord_108783).sum := by decide
  have hdescent : baseEnd_108783 < baseStart_108783 := by decide
  rcases family_descends (prefixWord ++ tailWord_108783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108831 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 2]
def baseStart_108831 : Nat := 118140960795 + 108831 * 2 ^ 59
def prefixEnd_108831 : Nat := 4983230072969 + 3 ^ 40 * 108831 * 2
def baseEnd_108831 : Nat := 49673433875172383921779

theorem tailTrace_108831 : CollatzResearch.WordTrace tailWord_108831 prefixEnd_108831 49673433875172383921779 := by
  unfold tailWord_108831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969392668731348700134347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2646261779154232466756231 3969392668731348700134347)
  ·
    refine ⟨5954089003097023050201521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3969392668731348700134347 5954089003097023050201521)
    ·
      refine ⟨4465566752322767287651141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5954089003097023050201521 4465566752322767287651141)
      ·
        refine ⟨837293766060518866434589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4465566752322767287651141 837293766060518866434589)
        ·
          refine ⟨313985162272694574912971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 837293766060518866434589 313985162272694574912971)
          ·
            refine ⟨470977743409041862369457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313985162272694574912971 470977743409041862369457)
            ·
              refine ⟨353233307556781396777093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470977743409041862369457 353233307556781396777093)
              ·
                refine ⟨66231245166896511895705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353233307556781396777093 66231245166896511895705)
                ·
                  refine ⟨49673433875172383921779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66231245166896511895705 49673433875172383921779)
                  ·
                    rfl

theorem cell20_108831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 2].length) (baseStart_108831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108831 prefixEnd_108831 := by exact prefixLift 108831
  have htrace : WordTrace (prefixWord ++ tailWord_108831) baseStart_108831 baseEnd_108831 := by
    simpa [prefixWord, tailWord_108831, baseEnd_108831] using wordTrace_append hprefix tailTrace_108831
  have hstable : (prefixWord ++ tailWord_108831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108831).length < 2 ^ (prefixWord ++ tailWord_108831).sum := by decide
  have hdescent : baseEnd_108831 < baseStart_108831 := by decide
  rcases family_descends (prefixWord ++ tailWord_108831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108865 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 2]
def baseStart_108865 : Nat := 118140960795 + 108865 * 2 ^ 59
def prefixEnd_108865 : Nat := 4983230072969 + 3 ^ 40 * 108865 * 2
def baseEnd_108865 : Nat := 49688952401619376788307

theorem tailTrace_108865 : CollatzResearch.WordTrace tailWord_108865 prefixEnd_108865 49688952401619376788307 := by
  unfold tailWord_108865
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970632750608172506872049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2647088500405448337914699 3970632750608172506872049)
  ·
    refine ⟨2977974562956129380154037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3970632750608172506872049 2977974562956129380154037)
    ·
      refine ⟨279185115277137129389441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2977974562956129380154037 279185115277137129389441)
      ·
        refine ⟨209388836457852847042081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279185115277137129389441 209388836457852847042081)
        ·
          refine ⟨157041627343389635281561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209388836457852847042081 157041627343389635281561)
          ·
            refine ⟨117781220507542226461171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157041627343389635281561 117781220507542226461171)
            ·
              refine ⟨176671830761313339691757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117781220507542226461171 176671830761313339691757)
              ·
                refine ⟨66251936535492502384409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176671830761313339691757 66251936535492502384409)
                ·
                  refine ⟨49688952401619376788307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66251936535492502384409 49688952401619376788307)
                  ·
                    rfl

theorem cell20_108865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_108865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108865 prefixEnd_108865 := by exact prefixLift 108865
  have htrace : WordTrace (prefixWord ++ tailWord_108865) baseStart_108865 baseEnd_108865 := by
    simpa [prefixWord, tailWord_108865, baseEnd_108865] using wordTrace_append hprefix tailTrace_108865
  have hstable : (prefixWord ++ tailWord_108865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108865).length < 2 ^ (prefixWord ++ tailWord_108865).sum := by decide
  have hdescent : baseEnd_108865 < baseStart_108865 := by decide
  rcases family_descends (prefixWord ++ tailWord_108865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108880 : List Nat := [2, 1, 1, 1, 1, 6, 8]
def baseStart_108880 : Nat := 118140960795 + 108880 * 2 ^ 59
def prefixEnd_108880 : Nat := 4983230072969 + 3 ^ 40 * 108880 * 2
def baseEnd_108880 : Nat := 5521755423371776809805

theorem tailTrace_108880 : CollatzResearch.WordTrace tailWord_108880 prefixEnd_108880 5521755423371776809805 := by
  unfold tailWord_108880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985589922776915034334047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2647453230369220045778729 1985589922776915034334047)
  ·
    refine ⟨2978384884165372551501071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1985589922776915034334047 2978384884165372551501071)
    ·
      refine ⟨4467577326248058827251607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978384884165372551501071 4467577326248058827251607)
      ·
        refine ⟨6701365989372088240877411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467577326248058827251607 6701365989372088240877411)
        ·
          refine ⟨10052048984058132361316117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701365989372088240877411 10052048984058132361316117)
          ·
            refine ⟨471189796127724954436693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10052048984058132361316117 471189796127724954436693)
            ·
              refine ⟨5521755423371776809805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 471189796127724954436693 5521755423371776809805)
              ·
                rfl

theorem cell20_108880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_108880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108880 prefixEnd_108880 := by exact prefixLift 108880
  have htrace : WordTrace (prefixWord ++ tailWord_108880) baseStart_108880 baseEnd_108880 := by
    simpa [prefixWord, tailWord_108880, baseEnd_108880] using wordTrace_append hprefix tailTrace_108880
  have hstable : (prefixWord ++ tailWord_108880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108880).length < 2 ^ (prefixWord ++ tailWord_108880).sum := by decide
  have hdescent : baseEnd_108880 < baseStart_108880 := by decide
  rcases family_descends (prefixWord ++ tailWord_108880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108949 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_108949 : Nat := 118140960795 + 108949 * 2 ^ 59
def prefixEnd_108949 : Nat := 4983230072969 + 3 ^ 40 * 108949 * 2
def baseEnd_108949 : Nat := 49727292290488417987963

theorem tailTrace_108949 : CollatzResearch.WordTrace tailWord_108949 prefixEnd_108949 49727292290488417987963 := by
  unfold tailWord_108949
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973696482303854852929901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2649130988202569901953267 3973696482303854852929901)
  ·
    refine ⟨1490136180863945569848713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3973696482303854852929901 1490136180863945569848713)
    ·
      refine ⟨1117602135647959177386535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1490136180863945569848713 1117602135647959177386535)
      ·
        refine ⟨1676403203471938766079803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117602135647959177386535 1676403203471938766079803)
        ·
          refine ⟨2514604805207908149119705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676403203471938766079803 2514604805207908149119705)
          ·
            refine ⟨1885953603905931111839779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514604805207908149119705 1885953603905931111839779)
            ·
              refine ⟨2828930405858896667759669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885953603905931111839779 2828930405858896667759669)
              ·
                refine ⟨265212225549271562602469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2828930405858896667759669 265212225549271562602469)
                ·
                  refine ⟨49727292290488417987963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265212225549271562602469 49727292290488417987963)
                  ·
                    rfl

theorem cell20_108949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_108949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108949 prefixEnd_108949 := by exact prefixLift 108949
  have htrace : WordTrace (prefixWord ++ tailWord_108949) baseStart_108949 baseEnd_108949 := by
    simpa [prefixWord, tailWord_108949, baseEnd_108949] using wordTrace_append hprefix tailTrace_108949
  have hstable : (prefixWord ++ tailWord_108949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108949).length < 2 ^ (prefixWord ++ tailWord_108949).sum := by decide
  have hdescent : baseEnd_108949 < baseStart_108949 := by decide
  rcases family_descends (prefixWord ++ tailWord_108949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108952 : List Nat := [2, 1, 2, 5, 1, 3, 1, 5]
def baseStart_108952 : Nat := 118140960795 + 108952 * 2 ^ 59
def prefixEnd_108952 : Nat := 4983230072969 + 3 ^ 40 * 108952 * 2
def baseEnd_108952 : Nat := 16576220524077913629317

theorem tailTrace_108952 : CollatzResearch.WordTrace tailWord_108952 prefixEnd_108952 16576220524077913629317 := by
  unfold tailWord_108952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986902950646493182644555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2649203934195324243526073 1986902950646493182644555)
  ·
    refine ⟨2980354425969739773966833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1986902950646493182644555 2980354425969739773966833)
    ·
      refine ⟨2235265819477304830475125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2980354425969739773966833 2235265819477304830475125)
      ·
        refine ⟨209556170575997327857043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2235265819477304830475125 209556170575997327857043)
        ·
          refine ⟨314334255863995991785565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209556170575997327857043 314334255863995991785565)
          ·
            refine ⟨117875345948998496919587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314334255863995991785565 117875345948998496919587)
            ·
              refine ⟨176813018923497745379381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117875345948998496919587 176813018923497745379381)
              ·
                refine ⟨16576220524077913629317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176813018923497745379381 16576220524077913629317)
                ·
                  rfl

theorem cell20_108952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_108952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108952 prefixEnd_108952 := by exact prefixLift 108952
  have htrace : WordTrace (prefixWord ++ tailWord_108952) baseStart_108952 baseEnd_108952 := by
    simpa [prefixWord, tailWord_108952, baseEnd_108952] using wordTrace_append hprefix tailTrace_108952
  have hstable : (prefixWord ++ tailWord_108952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108952).length < 2 ^ (prefixWord ++ tailWord_108952).sum := by decide
  have hdescent : baseEnd_108952 < baseStart_108952 := by decide
  rcases family_descends (prefixWord ++ tailWord_108952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108983 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 2]
def baseStart_108983 : Nat := 118140960795 + 108983 * 2 ^ 59
def prefixEnd_108983 : Nat := 4983230072969 + 3 ^ 40 * 108983 * 2
def baseEnd_108983 : Nat := 49742810816935410854491

theorem tailTrace_108983 : CollatzResearch.WordTrace tailWord_108983 prefixEnd_108983 49742810816935410854491 := by
  unfold tailWord_108983
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974936564180678659667603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2649957709453785773111735 3974936564180678659667603)
  ·
    refine ⟨5962404846271017989501405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3974936564180678659667603 5962404846271017989501405)
    ·
      refine ⟨2235901817351631746063027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5962404846271017989501405 2235901817351631746063027)
      ·
        refine ⟨3353852726027447619094541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235901817351631746063027 3353852726027447619094541)
        ·
          refine ⟨1257694772260292857160453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3353852726027447619094541 1257694772260292857160453)
          ·
            refine ⟨235817769798804910717585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1257694772260292857160453 235817769798804910717585)
            ·
              refine ⟨176863327349103683038189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235817769798804910717585 176863327349103683038189)
              ·
                refine ⟨66323747755913881139321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176863327349103683038189 66323747755913881139321)
                ·
                  refine ⟨49742810816935410854491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66323747755913881139321 49742810816935410854491)
                  ·
                    rfl

theorem cell20_108983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 2].length) (baseStart_108983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108983 prefixEnd_108983 := by exact prefixLift 108983
  have htrace : WordTrace (prefixWord ++ tailWord_108983) baseStart_108983 baseEnd_108983 := by
    simpa [prefixWord, tailWord_108983, baseEnd_108983] using wordTrace_append hprefix tailTrace_108983
  have hstable : (prefixWord ++ tailWord_108983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108983).length < 2 ^ (prefixWord ++ tailWord_108983).sum := by decide
  have hdescent : baseEnd_108983 < baseStart_108983 := by decide
  rcases family_descends (prefixWord ++ tailWord_108983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108993 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 5]
def baseStart_108993 : Nat := 118140960795 + 108993 * 2 ^ 59
def prefixEnd_108993 : Nat := 4983230072969 + 3 ^ 40 * 108993 * 2
def baseEnd_108993 : Nat := 49747375089419820521117

theorem tailTrace_108993 : CollatzResearch.WordTrace tailWord_108993 prefixEnd_108993 49747375089419820521117 := by
  unfold tailWord_108993
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975301294144450367531633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2650200862762966911687755 3975301294144450367531633)
  ·
    refine ⟨2981475970608337775648725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3975301294144450367531633 2981475970608337775648725)
    ·
      refine ⟨69878343061132916616767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2981475970608337775648725 69878343061132916616767)
      ·
        refine ⟨104817514591699374925151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69878343061132916616767 104817514591699374925151)
        ·
          refine ⟨157226271887549062387727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104817514591699374925151 157226271887549062387727)
          ·
            refine ⟨235839407831323593581591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157226271887549062387727 235839407831323593581591)
            ·
              refine ⟨353759111746985390372387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235839407831323593581591 353759111746985390372387)
              ·
                refine ⟨530638667620478085558581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353759111746985390372387 530638667620478085558581)
                ·
                  refine ⟨49747375089419820521117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530638667620478085558581 49747375089419820521117)
                  ·
                    rfl

theorem cell20_108993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_108993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108993 prefixEnd_108993 := by exact prefixLift 108993
  have htrace : WordTrace (prefixWord ++ tailWord_108993) baseStart_108993 baseEnd_108993 := by
    simpa [prefixWord, tailWord_108993, baseEnd_108993] using wordTrace_append hprefix tailTrace_108993
  have hstable : (prefixWord ++ tailWord_108993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108993).length < 2 ^ (prefixWord ++ tailWord_108993).sum := by decide
  have hdescent : baseEnd_108993 < baseStart_108993 := by decide
  rcases family_descends (prefixWord ++ tailWord_108993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109025 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_109025 : Nat := 118140960795 + 109025 * 2 ^ 59
def prefixEnd_109025 : Nat := 4983230072969 + 3 ^ 40 * 109025 * 2
def baseEnd_109025 : Nat := 49761980761369931454319

theorem tailTrace_109025 : CollatzResearch.WordTrace tailWord_109025 prefixEnd_109025 49761980761369931454319 := by
  unfold tailWord_109025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976468430028519832696529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2650978953352346555131019 3976468430028519832696529)
  ·
    refine ⟨2982351322521389874522397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3976468430028519832696529 2982351322521389874522397)
    ·
      refine ⟨1118381745945521202945899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2982351322521389874522397 1118381745945521202945899)
      ·
        refine ⟨1677572618918281804418849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118381745945521202945899 1677572618918281804418849)
        ·
          refine ⟨1258179464188711353314137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677572618918281804418849 1258179464188711353314137)
          ·
            refine ⟨943634598141533514985603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1258179464188711353314137 943634598141533514985603)
            ·
              refine ⟨1415451897212300272478405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943634598141533514985603 1415451897212300272478405)
              ·
                refine ⟨265397230727306301089701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1415451897212300272478405 265397230727306301089701)
                ·
                  refine ⟨49761980761369931454319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265397230727306301089701 49761980761369931454319)
                  ·
                    rfl

theorem cell20_109025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_109025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109025 prefixEnd_109025 := by exact prefixLift 109025
  have htrace : WordTrace (prefixWord ++ tailWord_109025) baseStart_109025 baseEnd_109025 := by
    simpa [prefixWord, tailWord_109025, baseEnd_109025] using wordTrace_append hprefix tailTrace_109025
  have hstable : (prefixWord ++ tailWord_109025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109025).length < 2 ^ (prefixWord ++ tailWord_109025).sum := by decide
  have hdescent : baseEnd_109025 < baseStart_109025 := by decide
  rcases family_descends (prefixWord ++ tailWord_109025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109038 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_109038 : Nat := 118140960795 + 109038 * 2 ^ 59
def prefixEnd_109038 : Nat := 4983230072969 + 3 ^ 40 * 109038 * 2
def baseEnd_109038 : Nat := 49767914315599664020933

theorem tailTrace_109038 : CollatzResearch.WordTrace tailWord_109038 prefixEnd_109038 49767914315599664020933 := by
  unfold tailWord_109038
  simp only [CollatzResearch.WordTrace]
  refine ⟨497117822372677881614971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2651295052654282035279845 497117822372677881614971)
  ·
    refine ⟨745676733559016822422457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 497117822372677881614971 745676733559016822422457)
    ·
      refine ⟨559257550169262616816843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 745676733559016822422457 559257550169262616816843)
      ·
        refine ⟨838886325253893925225265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559257550169262616816843 838886325253893925225265)
        ·
          refine ⟨629164743940420443918949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838886325253893925225265 629164743940420443918949)
          ·
            refine ⟨117968389488828833234803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 629164743940420443918949 117968389488828833234803)
            ·
              refine ⟨176952584233243249852205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117968389488828833234803 176952584233243249852205)
              ·
                refine ⟨66357219087466218694577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176952584233243249852205 66357219087466218694577)
                ·
                  refine ⟨49767914315599664020933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66357219087466218694577 49767914315599664020933)
                  ·
                    rfl

theorem cell20_109038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_109038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109038 prefixEnd_109038 := by exact prefixLift 109038
  have htrace : WordTrace (prefixWord ++ tailWord_109038) baseStart_109038 baseEnd_109038 := by
    simpa [prefixWord, tailWord_109038, baseEnd_109038] using wordTrace_append hprefix tailTrace_109038
  have hstable : (prefixWord ++ tailWord_109038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109038).length < 2 ^ (prefixWord ++ tailWord_109038).sum := by decide
  have hdescent : baseEnd_109038 < baseStart_109038 := by decide
  rcases family_descends (prefixWord ++ tailWord_109038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109045 : List Nat := [1, 3, 5, 1, 3, 1, 6]
def baseStart_109045 : Nat := 118140960795 + 109045 * 2 ^ 59
def prefixEnd_109045 : Nat := 4983230072969 + 3 ^ 40 * 109045 * 2
def baseEnd_109045 : Nat := 5530123256259861198619

theorem tailTrace_109045 : CollatzResearch.WordTrace tailWord_109045 prefixEnd_109045 5530123256259861198619 := by
  unfold tailWord_109045
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977197889956063248424589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651465259970708832283059 3977197889956063248424589)
  ·
    refine ⟨1491449208733523718159221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3977197889956063248424589 1491449208733523718159221)
    ·
      refine ⟨139823363318767848577427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1491449208733523718159221 139823363318767848577427)
      ·
        refine ⟨209735044978151772866141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139823363318767848577427 209735044978151772866141)
        ·
          refine ⟨78650641866806914824803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209735044978151772866141 78650641866806914824803)
          ·
            refine ⟨117975962800210372237205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78650641866806914824803 117975962800210372237205)
            ·
              refine ⟨5530123256259861198619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117975962800210372237205 5530123256259861198619)
              ·
                rfl

theorem cell20_109045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 6].length) (baseStart_109045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109045 prefixEnd_109045 := by exact prefixLift 109045
  have htrace : WordTrace (prefixWord ++ tailWord_109045) baseStart_109045 baseEnd_109045 := by
    simpa [prefixWord, tailWord_109045, baseEnd_109045] using wordTrace_append hprefix tailTrace_109045
  have hstable : (prefixWord ++ tailWord_109045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109045).length < 2 ^ (prefixWord ++ tailWord_109045).sum := by decide
  have hdescent : baseEnd_109045 < baseStart_109045 := by decide
  rcases family_descends (prefixWord ++ tailWord_109045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109059 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 2]
def baseStart_109059 : Nat := 118140960795 + 109059 * 2 ^ 59
def prefixEnd_109059 : Nat := 4983230072969 + 3 ^ 40 * 109059 * 2
def baseEnd_109059 : Nat := 49777499287816924320847

theorem tailTrace_109059 : CollatzResearch.WordTrace tailWord_109059 prefixEnd_109059 49777499287816924320847 := by
  unfold tailWord_109059
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977708511905343639434231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651805674603562426289487 3977708511905343639434231)
  ·
    refine ⟨5966562767858015459151347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977708511905343639434231 5966562767858015459151347)
    ·
      refine ⟨8949844151787023188727021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5966562767858015459151347 8949844151787023188727021)
      ·
        refine ⟨3356191556920133695772633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8949844151787023188727021 3356191556920133695772633)
        ·
          refine ⟨2517143667690100271829475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356191556920133695772633 2517143667690100271829475)
          ·
            refine ⟨3775715501535150407744213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517143667690100271829475 3775715501535150407744213)
            ·
              refine ⟨88493332067230087681505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3775715501535150407744213 88493332067230087681505)
              ·
                refine ⟨66369999050422565761129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88493332067230087681505 66369999050422565761129)
                ·
                  refine ⟨49777499287816924320847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66369999050422565761129 49777499287816924320847)
                  ·
                    rfl

theorem cell20_109059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 2].length) (baseStart_109059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109059 prefixEnd_109059 := by exact prefixLift 109059
  have htrace : WordTrace (prefixWord ++ tailWord_109059) baseStart_109059 baseEnd_109059 := by
    simpa [prefixWord, tailWord_109059, baseEnd_109059] using wordTrace_append hprefix tailTrace_109059
  have hstable : (prefixWord ++ tailWord_109059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109059).length < 2 ^ (prefixWord ++ tailWord_109059).sum := by decide
  have hdescent : baseEnd_109059 < baseStart_109059 := by decide
  rcases family_descends (prefixWord ++ tailWord_109059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109062 : List Nat := [6, 2, 1, 1, 1, 2, 2, 5]
def baseStart_109062 : Nat := 118140960795 + 109062 * 2 ^ 59
def prefixEnd_109062 : Nat := 4983230072969 + 3 ^ 40 * 109062 * 2
def baseEnd_109062 : Nat := 16592956189854082406945

theorem tailTrace_109062 : CollatzResearch.WordTrace tailWord_109062 prefixEnd_109062 16592956189854082406945 := by
  unfold tailWord_109062
  simp only [CollatzResearch.WordTrace]
  refine ⟨124306810340452348493545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2651878620596316767862293 124306810340452348493545)
  ·
    refine ⟨93230107755339261370159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124306810340452348493545 93230107755339261370159)
    ·
      refine ⟨139845161633008892055239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93230107755339261370159 139845161633008892055239)
      ·
        refine ⟨209767742449513338082859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139845161633008892055239 209767742449513338082859)
        ·
          refine ⟨314651613674270007124289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209767742449513338082859 314651613674270007124289)
          ·
            refine ⟨235988710255702505343217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314651613674270007124289 235988710255702505343217)
            ·
              refine ⟨176991532691776879007413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235988710255702505343217 176991532691776879007413)
              ·
                refine ⟨16592956189854082406945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176991532691776879007413 16592956189854082406945)
                ·
                  rfl

theorem cell20_109062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_109062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109062 prefixEnd_109062 := by exact prefixLift 109062
  have htrace : WordTrace (prefixWord ++ tailWord_109062) baseStart_109062 baseEnd_109062 := by
    simpa [prefixWord, tailWord_109062, baseEnd_109062] using wordTrace_append hprefix tailTrace_109062
  have hstable : (prefixWord ++ tailWord_109062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109062).length < 2 ^ (prefixWord ++ tailWord_109062).sum := by decide
  have hdescent : baseEnd_109062 < baseStart_109062 := by decide
  rcases family_descends (prefixWord ++ tailWord_109062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109069 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 3]
def baseStart_109069 : Nat := 118140960795 + 109069 * 2 ^ 59
def prefixEnd_109069 : Nat := 4983230072969 + 3 ^ 40 * 109069 * 2
def baseEnd_109069 : Nat := 49782063560301333987473

theorem tailTrace_109069 : CollatzResearch.WordTrace tailWord_109069 prefixEnd_109069 49782063560301333987473 := by
  unfold tailWord_109069
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978073241869115347298261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2652048827912743564865507 3978073241869115347298261)
  ·
    refine ⟨93236091606307390952303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3978073241869115347298261 93236091606307390952303)
    ·
      refine ⟨139854137409461086428455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93236091606307390952303 139854137409461086428455)
      ·
        refine ⟨209781206114191629642683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139854137409461086428455 209781206114191629642683)
        ·
          refine ⟨314671809171287444464025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209781206114191629642683 314671809171287444464025)
          ·
            refine ⟨236003856878465583348019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314671809171287444464025 236003856878465583348019)
            ·
              refine ⟨354005785317698375022029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236003856878465583348019 354005785317698375022029)
              ·
                refine ⟨132752169494136890633261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354005785317698375022029 132752169494136890633261)
                ·
                  refine ⟨49782063560301333987473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132752169494136890633261 49782063560301333987473)
                  ·
                    rfl

theorem cell20_109069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_109069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109069 prefixEnd_109069 := by exact prefixLift 109069
  have htrace : WordTrace (prefixWord ++ tailWord_109069) baseStart_109069 baseEnd_109069 := by
    simpa [prefixWord, tailWord_109069, baseEnd_109069] using wordTrace_append hprefix tailTrace_109069
  have hstable : (prefixWord ++ tailWord_109069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109069).length < 2 ^ (prefixWord ++ tailWord_109069).sum := by decide
  have hdescent : baseEnd_109069 < baseStart_109069 := by decide
  rcases family_descends (prefixWord ++ tailWord_109069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109114 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_109114 : Nat := 118140960795 + 109114 * 2 ^ 59
def prefixEnd_109114 : Nat := 4983230072969 + 3 ^ 40 * 109114 * 2
def baseEnd_109114 : Nat := 49802602786481177487289

theorem tailTrace_109114 : CollatzResearch.WordTrace tailWord_109114 prefixEnd_109114 49802602786481177487289 := by
  unfold tailWord_109114
  simp only [CollatzResearch.WordTrace]
  refine ⟨994928631676522008171599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2653143017804058688457597 994928631676522008171599)
  ·
    refine ⟨1492392947514783012257399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994928631676522008171599 1492392947514783012257399)
    ·
      refine ⟨2238589421272174518386099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492392947514783012257399 2238589421272174518386099)
      ·
        refine ⟨3357884131908261777579149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238589421272174518386099 3357884131908261777579149)
        ·
          refine ⟨1259206549465598166592181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3357884131908261777579149 1259206549465598166592181)
          ·
            refine ⟨118050614012399828118017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1259206549465598166592181 118050614012399828118017)
            ·
              refine ⟨88537960509299871088513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118050614012399828118017 88537960509299871088513)
              ·
                refine ⟨66403470381974903316385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88537960509299871088513 66403470381974903316385)
                ·
                  refine ⟨49802602786481177487289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66403470381974903316385 49802602786481177487289)
                  ·
                    rfl

theorem cell20_109114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_109114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109114 prefixEnd_109114 := by exact prefixLift 109114
  have htrace : WordTrace (prefixWord ++ tailWord_109114) baseStart_109114 baseEnd_109114 := by
    simpa [prefixWord, tailWord_109114, baseEnd_109114] using wordTrace_append hprefix tailTrace_109114
  have hstable : (prefixWord ++ tailWord_109114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109114).length < 2 ^ (prefixWord ++ tailWord_109114).sum := by decide
  have hdescent : baseEnd_109114 < baseStart_109114 := by decide
  rcases family_descends (prefixWord ++ tailWord_109114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109125 : List Nat := [1, 3, 1, 1, 1, 7, 1, 5]
def baseStart_109125 : Nat := 118140960795 + 109125 * 2 ^ 59
def prefixEnd_109125 : Nat := 4983230072969 + 3 ^ 40 * 109125 * 2
def baseEnd_109125 : Nat := 16602541162071342706859

theorem tailTrace_109125 : CollatzResearch.WordTrace tailWord_109125 prefixEnd_109125 16602541162071342706859 := by
  unfold tailWord_109125
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980115729666236911336829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2653410486444157940891219 3980115729666236911336829)
  ·
    refine ⟨1492543398624838841751311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3980115729666236911336829 1492543398624838841751311)
    ·
      refine ⟨2238815097937258262626967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492543398624838841751311 2238815097937258262626967)
      ·
        refine ⟨3358222646905887393940451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238815097937258262626967 3358222646905887393940451)
        ·
          refine ⟨5037333970358831090910677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358222646905887393940451 5037333970358831090910677)
          ·
            refine ⟨118062514930285103693219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5037333970358831090910677 118062514930285103693219)
            ·
              refine ⟨177093772395427655539829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118062514930285103693219 177093772395427655539829)
              ·
                refine ⟨16602541162071342706859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177093772395427655539829 16602541162071342706859)
                ·
                  rfl

theorem cell20_109125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_109125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109125 prefixEnd_109125 := by exact prefixLift 109125
  have htrace : WordTrace (prefixWord ++ tailWord_109125) baseStart_109125 baseEnd_109125 := by
    simpa [prefixWord, tailWord_109125, baseEnd_109125] using wordTrace_append hprefix tailTrace_109125
  have hstable : (prefixWord ++ tailWord_109125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109125).length < 2 ^ (prefixWord ++ tailWord_109125).sum := by decide
  have hdescent : baseEnd_109125 < baseStart_109125 := by decide
  rcases family_descends (prefixWord ++ tailWord_109125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109132 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_109132 : Nat := 118140960795 + 109132 * 2 ^ 59
def prefixEnd_109132 : Nat := 4983230072969 + 3 ^ 40 * 109132 * 2
def baseEnd_109132 : Nat := 49810818476953114887215

theorem tailTrace_109132 : CollatzResearch.WordTrace tailWord_109132 prefixEnd_109132 49810818476953114887215 := by
  unfold tailWord_109132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990185520320438553420825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2653580693760584737894433 1990185520320438553420825)
  ·
    refine ⟨1492639140240328915065619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1990185520320438553420825 1492639140240328915065619)
    ·
      refine ⟨2238958710360493372598429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492639140240328915065619 2238958710360493372598429)
      ·
        refine ⟨839609516385185014724411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2238958710360493372598429 839609516385185014724411)
        ·
          refine ⟨1259414274577777522086617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839609516385185014724411 1259414274577777522086617)
          ·
            refine ⟨944560705933333141564963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259414274577777522086617 944560705933333141564963)
            ·
              refine ⟨1416841058899999712347445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944560705933333141564963 1416841058899999712347445)
              ·
                refine ⟨132828849271874973032573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1416841058899999712347445 132828849271874973032573)
                ·
                  refine ⟨49810818476953114887215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132828849271874973032573 49810818476953114887215)
                  ·
                    rfl

theorem cell20_109132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_109132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109132 prefixEnd_109132 := by exact prefixLift 109132
  have htrace : WordTrace (prefixWord ++ tailWord_109132) baseStart_109132 baseEnd_109132 := by
    simpa [prefixWord, tailWord_109132, baseEnd_109132] using wordTrace_append hprefix tailTrace_109132
  have hstable : (prefixWord ++ tailWord_109132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109132).length < 2 ^ (prefixWord ++ tailWord_109132).sum := by decide
  have hdescent : baseEnd_109132 < baseStart_109132 := by decide
  rcases family_descends (prefixWord ++ tailWord_109132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109166 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_109166 : Nat := 118140960795 + 109166 * 2 ^ 59
def prefixEnd_109166 : Nat := 4983230072969 + 3 ^ 40 * 109166 * 2
def baseEnd_109166 : Nat := 49826337003400107753743

theorem tailTrace_109166 : CollatzResearch.WordTrace tailWord_109166 prefixEnd_109166 49826337003400107753743 := by
  unfold tailWord_109166
  simp only [CollatzResearch.WordTrace]
  refine ⟨497701390314712614197419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2654407415011800609052901 497701390314712614197419)
  ·
    refine ⟨746552085472068921296129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 497701390314712614197419 746552085472068921296129)
    ·
      refine ⟨559914064104051690972097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 746552085472068921296129 559914064104051690972097)
      ·
        refine ⟨419935548078038768229073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559914064104051690972097 419935548078038768229073)
        ·
          refine ⟨314951661058529076171805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419935548078038768229073 314951661058529076171805)
          ·
            refine ⟨118106872896948403564427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314951661058529076171805 118106872896948403564427)
            ·
              refine ⟨177160309345422605346641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118106872896948403564427 177160309345422605346641)
              ·
                refine ⟨132870232009066954009981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177160309345422605346641 132870232009066954009981)
                ·
                  refine ⟨49826337003400107753743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132870232009066954009981 49826337003400107753743)
                  ·
                    rfl

theorem cell20_109166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_109166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109166 prefixEnd_109166 := by exact prefixLift 109166
  have htrace : WordTrace (prefixWord ++ tailWord_109166) baseStart_109166 baseEnd_109166 := by
    simpa [prefixWord, tailWord_109166, baseEnd_109166] using wordTrace_append hprefix tailTrace_109166
  have hstable : (prefixWord ++ tailWord_109166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109166).length < 2 ^ (prefixWord ++ tailWord_109166).sum := by decide
  have hdescent : baseEnd_109166 < baseStart_109166 := by decide
  rcases family_descends (prefixWord ++ tailWord_109166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109173 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_109173 : Nat := 118140960795 + 109173 * 2 ^ 59
def prefixEnd_109173 : Nat := 4983230072969 + 3 ^ 40 * 109173 * 2
def baseEnd_109173 : Nat := 49829531994139194520381

theorem tailTrace_109173 : CollatzResearch.WordTrace tailWord_109173 prefixEnd_109173 49829531994139194520381 := by
  unfold tailWord_109173
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981866433492341109084173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2654577622328227406056115 3981866433492341109084173)
  ·
    refine ⟨1493199912559627915906565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3981866433492341109084173 1493199912559627915906565)
    ·
      refine ⟨279974983604930234232481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1493199912559627915906565 279974983604930234232481)
      ·
        refine ⟨209981237703697675674361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279974983604930234232481 209981237703697675674361)
        ·
          refine ⟨157485928277773256755771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209981237703697675674361 157485928277773256755771)
          ·
            refine ⟨236228892416659885133657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157485928277773256755771 236228892416659885133657)
            ·
              refine ⟨177171669312494913850243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236228892416659885133657 177171669312494913850243)
              ·
                refine ⟨265757503968742370775365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177171669312494913850243 265757503968742370775365)
                ·
                  refine ⟨49829531994139194520381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265757503968742370775365 49829531994139194520381)
                  ·
                    rfl

theorem cell20_109173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_109173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109173 prefixEnd_109173 := by exact prefixLift 109173
  have htrace : WordTrace (prefixWord ++ tailWord_109173) baseStart_109173 baseEnd_109173 := by
    simpa [prefixWord, tailWord_109173, baseEnd_109173] using wordTrace_append hprefix tailTrace_109173
  have hstable : (prefixWord ++ tailWord_109173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109173).length < 2 ^ (prefixWord ++ tailWord_109173).sum := by decide
  have hdescent : baseEnd_109173 < baseStart_109173 := by decide
  rcases family_descends (prefixWord ++ tailWord_109173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109177 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_109177 : Nat := 118140960795 + 109177 * 2 ^ 59
def prefixEnd_109177 : Nat := 4983230072969 + 3 ^ 40 * 109177 * 2
def baseEnd_109177 : Nat := 49831357703132958387031

theorem tailTrace_109177 : CollatzResearch.WordTrace tailWord_109177 prefixEnd_109177 49831357703132958387031 := by
  unfold tailWord_109177
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982012325477849792229785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2654674883651899861486523 3982012325477849792229785)
  ·
    refine ⟨2986509244108387344172339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3982012325477849792229785 2986509244108387344172339)
    ·
      refine ⟨4479763866162581016258509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986509244108387344172339 4479763866162581016258509)
      ·
        refine ⟨1679911449810967881096941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4479763866162581016258509 1679911449810967881096941)
        ·
          refine ⟨629966793679112955411353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1679911449810967881096941 629966793679112955411353)
          ·
            refine ⟨472475095259334716558515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629966793679112955411353 472475095259334716558515)
            ·
              refine ⟨708712642889002074837773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472475095259334716558515 708712642889002074837773)
              ·
                refine ⟨265767241083375778064165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708712642889002074837773 265767241083375778064165)
                ·
                  refine ⟨49831357703132958387031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265767241083375778064165 49831357703132958387031)
                  ·
                    rfl

theorem cell20_109177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_109177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109177 prefixEnd_109177 := by exact prefixLift 109177
  have htrace : WordTrace (prefixWord ++ tailWord_109177) baseStart_109177 baseEnd_109177 := by
    simpa [prefixWord, tailWord_109177, baseEnd_109177] using wordTrace_append hprefix tailTrace_109177
  have hstable : (prefixWord ++ tailWord_109177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109177).length < 2 ^ (prefixWord ++ tailWord_109177).sum := by decide
  have hdescent : baseEnd_109177 < baseStart_109177 := by decide
  rcases family_descends (prefixWord ++ tailWord_109177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109238 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_109238 : Nat := 118140960795 + 109238 * 2 ^ 59
def prefixEnd_109238 : Nat := 4983230072969 + 3 ^ 40 * 109238 * 2
def baseEnd_109238 : Nat := 49859199765287857353449

theorem tailTrace_109238 : CollatzResearch.WordTrace tailWord_109238 prefixEnd_109238 49859199765287857353449 := by
  unfold tailWord_109238
  simp only [CollatzResearch.WordTrace]
  refine ⟨249014823641053575637523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2656158118837904806800245 249014823641053575637523)
  ·
    refine ⟨373522235461580363456285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249014823641053575637523 373522235461580363456285)
    ·
      refine ⟨140070838298092636296107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373522235461580363456285 140070838298092636296107)
      ·
        refine ⟨210106257447138954444161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140070838298092636296107 210106257447138954444161)
        ·
          refine ⟨157579693085354215833121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210106257447138954444161 157579693085354215833121)
          ·
            refine ⟨118184769814015661874841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157579693085354215833121 118184769814015661874841)
            ·
              refine ⟨88638577360511746406131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118184769814015661874841 88638577360511746406131)
              ·
                refine ⟨132957866040767619609197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88638577360511746406131 132957866040767619609197)
                ·
                  refine ⟨49859199765287857353449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132957866040767619609197 49859199765287857353449)
                  ·
                    rfl

theorem cell20_109238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_109238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109238 prefixEnd_109238 := by exact prefixLift 109238
  have htrace : WordTrace (prefixWord ++ tailWord_109238) baseStart_109238 baseEnd_109238 := by
    simpa [prefixWord, tailWord_109238, baseEnd_109238] using wordTrace_append hprefix tailTrace_109238
  have hstable : (prefixWord ++ tailWord_109238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109238).length < 2 ^ (prefixWord ++ tailWord_109238).sum := by decide
  have hdescent : baseEnd_109238 < baseStart_109238 := by decide
  rcases family_descends (prefixWord ++ tailWord_109238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109239 : List Nat := [1, 1, 3, 1, 6, 1, 2, 5]
def baseStart_109239 : Nat := 118140960795 + 109239 * 2 ^ 59
def prefixEnd_109239 : Nat := 4983230072969 + 3 ^ 40 * 109239 * 2
def baseEnd_109239 : Nat := 16619885397512099440037

theorem tailTrace_109239 : CollatzResearch.WordTrace tailWord_109239 prefixEnd_109239 16619885397512099440037 := by
  unfold tailWord_109239
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984273651253234380986771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2656182434168822920657847 3984273651253234380986771)
  ·
    refine ⟨5976410476879851571480157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3984273651253234380986771 5976410476879851571480157)
    ·
      refine ⟨2241153928829944339305059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5976410476879851571480157 2241153928829944339305059)
      ·
        refine ⟨3361730893244916508957589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241153928829944339305059 3361730893244916508957589)
        ·
          refine ⟨157581135620855461357387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3361730893244916508957589 157581135620855461357387)
          ·
            refine ⟨236371703431283192036081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157581135620855461357387 236371703431283192036081)
            ·
              refine ⟨177278777573462394027061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236371703431283192036081 177278777573462394027061)
              ·
                refine ⟨16619885397512099440037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177278777573462394027061 16619885397512099440037)
                ·
                  rfl

theorem cell20_109239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_109239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109239 prefixEnd_109239 := by exact prefixLift 109239
  have htrace : WordTrace (prefixWord ++ tailWord_109239) baseStart_109239 baseEnd_109239 := by
    simpa [prefixWord, tailWord_109239, baseEnd_109239] using wordTrace_append hprefix tailTrace_109239
  have hstable : (prefixWord ++ tailWord_109239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109239).length < 2 ^ (prefixWord ++ tailWord_109239).sum := by decide
  have hdescent : baseEnd_109239 < baseStart_109239 := by decide
  rcases family_descends (prefixWord ++ tailWord_109239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109284 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_109284 : Nat := 118140960795 + 109284 * 2 ^ 59
def prefixEnd_109284 : Nat := 4983230072969 + 3 ^ 40 * 109284 * 2
def baseEnd_109284 : Nat := 49880195418716141819927

theorem tailTrace_109284 : CollatzResearch.WordTrace tailWord_109284 prefixEnd_109284 49880195418716141819927 := by
  unfold tailWord_109284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992957468045103533187453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2657276624060138044249937 1992957468045103533187453)
  ·
    refine ⟨747359050516913824945295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1992957468045103533187453 747359050516913824945295)
    ·
      refine ⟨1121038575775370737417943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747359050516913824945295 1121038575775370737417943)
      ·
        refine ⟨1681557863663056106126915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121038575775370737417943 1681557863663056106126915)
        ·
          refine ⟨2522336795494584159190373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681557863663056106126915 2522336795494584159190373)
          ·
            refine ⟨472938149155234529848195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2522336795494584159190373 472938149155234529848195)
            ·
              refine ⟨709407223732851794772293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472938149155234529848195 709407223732851794772293)
              ·
                refine ⟨133013854449909711519805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709407223732851794772293 133013854449909711519805)
                ·
                  refine ⟨49880195418716141819927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133013854449909711519805 49880195418716141819927)
                  ·
                    rfl

theorem cell20_109284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_109284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109284 prefixEnd_109284 := by exact prefixLift 109284
  have htrace : WordTrace (prefixWord ++ tailWord_109284) baseStart_109284 baseEnd_109284 := by
    simpa [prefixWord, tailWord_109284, baseEnd_109284] using wordTrace_append hprefix tailTrace_109284
  have hstable : (prefixWord ++ tailWord_109284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109284).length < 2 ^ (prefixWord ++ tailWord_109284).sum := by decide
  have hdescent : baseEnd_109284 < baseStart_109284 := by decide
  rcases family_descends (prefixWord ++ tailWord_109284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109346 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_109346 : Nat := 118140960795 + 109346 * 2 ^ 59
def prefixEnd_109346 : Nat := 4983230072969 + 3 ^ 40 * 109346 * 2
def baseEnd_109346 : Nat := 49908493908119481753007

theorem tailTrace_109346 : CollatzResearch.WordTrace tailWord_109346 prefixEnd_109346 49908493908119481753007 := by
  unfold tailWord_109346
  simp only [CollatzResearch.WordTrace]
  refine ⟨997044065466397913782973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2658784174577061103421261 997044065466397913782973)
  ·
    refine ⟨373891524549899217668615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 997044065466397913782973 373891524549899217668615)
    ·
      refine ⟨560837286824848826502923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373891524549899217668615 560837286824848826502923)
      ·
        refine ⟨841255930237273239754385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560837286824848826502923 841255930237273239754385)
        ·
          refine ⟨630941947677954929815789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841255930237273239754385 630941947677954929815789)
          ·
            refine ⟨236603230379233098680921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630941947677954929815789 236603230379233098680921)
            ·
              refine ⟨177452422784424824010691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236603230379233098680921 177452422784424824010691)
              ·
                refine ⟨266178634176637236016037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177452422784424824010691 266178634176637236016037)
                ·
                  refine ⟨49908493908119481753007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266178634176637236016037 49908493908119481753007)
                  ·
                    rfl

theorem cell20_109346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_109346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109346 prefixEnd_109346 := by exact prefixLift 109346
  have htrace : WordTrace (prefixWord ++ tailWord_109346) baseStart_109346 baseEnd_109346 := by
    simpa [prefixWord, tailWord_109346, baseEnd_109346] using wordTrace_append hprefix tailTrace_109346
  have hstable : (prefixWord ++ tailWord_109346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109346).length < 2 ^ (prefixWord ++ tailWord_109346).sum := by decide
  have hdescent : baseEnd_109346 < baseStart_109346 := by decide
  rcases family_descends (prefixWord ++ tailWord_109346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109366 : List Nat := [5, 1, 2, 2, 3, 1, 2, 4]
def baseStart_109366 : Nat := 118140960795 + 109366 * 2 ^ 59
def prefixEnd_109366 : Nat := 4983230072969 + 3 ^ 40 * 109366 * 2
def baseEnd_109366 : Nat := 16639207484362767028753

theorem tailTrace_109366 : CollatzResearch.WordTrace tailWord_109366 prefixEnd_109366 16639207484362767028753 := by
  unfold tailWord_109366
  simp only [CollatzResearch.WordTrace]
  refine ⟨249306607612070941928747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2659270481195423380573301 249306607612070941928747)
  ·
    refine ⟨373959911418106412893121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249306607612070941928747 373959911418106412893121)
    ·
      refine ⟨280469933563579809669841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373959911418106412893121 280469933563579809669841)
      ·
        refine ⟨210352450172684857252381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280469933563579809669841 210352450172684857252381)
        ·
          refine ⟨78882168814756821469643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210352450172684857252381 78882168814756821469643)
          ·
            refine ⟨118323253222135232204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78882168814756821469643 118323253222135232204465)
            ·
              refine ⟨88742439916601424153349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118323253222135232204465 88742439916601424153349)
              ·
                refine ⟨16639207484362767028753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88742439916601424153349 16639207484362767028753)
                ·
                  rfl

theorem cell20_109366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_109366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109366 prefixEnd_109366 := by exact prefixLift 109366
  have htrace : WordTrace (prefixWord ++ tailWord_109366) baseStart_109366 baseEnd_109366 := by
    simpa [prefixWord, tailWord_109366, baseEnd_109366] using wordTrace_append hprefix tailTrace_109366
  have hstable : (prefixWord ++ tailWord_109366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109366).length < 2 ^ (prefixWord ++ tailWord_109366).sum := by decide
  have hdescent : baseEnd_109366 < baseStart_109366 := by decide
  rcases family_descends (prefixWord ++ tailWord_109366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109370 : List Nat := [3, 1, 1, 1, 6, 2, 2, 4]
def baseStart_109370 : Nat := 118140960795 + 109370 * 2 ^ 59
def prefixEnd_109370 : Nat := 4983230072969 + 3 ^ 40 * 109370 * 2
def baseEnd_109370 : Nat := 16639816054027354984303

theorem tailTrace_109370 : CollatzResearch.WordTrace tailWord_109370 prefixEnd_109370 16639816054027354984303 := by
  unfold tailWord_109370
  simp only [CollatzResearch.WordTrace]
  refine ⟨997262903444660938501391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2659367742519095836003709 997262903444660938501391)
  ·
    refine ⟨1495894355166991407752087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997262903444660938501391 1495894355166991407752087)
    ·
      refine ⟨2243841532750487111628131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495894355166991407752087 2243841532750487111628131)
      ·
        refine ⟨3365762299125730667442197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243841532750487111628131 3365762299125730667442197)
        ·
          refine ⟨157770107771518625036353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3365762299125730667442197 157770107771518625036353)
          ·
            refine ⟨118327580828638968777265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157770107771518625036353 118327580828638968777265)
            ·
              refine ⟨88745685621479226582949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118327580828638968777265 88745685621479226582949)
              ·
                refine ⟨16639816054027354984303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88745685621479226582949 16639816054027354984303)
                ·
                  rfl

theorem cell20_109370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_109370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109370 prefixEnd_109370 := by exact prefixLift 109370
  have htrace : WordTrace (prefixWord ++ tailWord_109370) baseStart_109370 baseEnd_109370 := by
    simpa [prefixWord, tailWord_109370, baseEnd_109370] using wordTrace_append hprefix tailTrace_109370
  have hstable : (prefixWord ++ tailWord_109370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109370).length < 2 ^ (prefixWord ++ tailWord_109370).sum := by decide
  have hdescent : baseEnd_109370 < baseStart_109370 := by decide
  rcases family_descends (prefixWord ++ tailWord_109370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109401 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 2]
def baseStart_109401 : Nat := 118140960795 + 109401 * 2 ^ 59
def prefixEnd_109401 : Nat := 4983230072969 + 3 ^ 40 * 109401 * 2
def baseEnd_109401 : Nat := 49933597406783734919449

theorem tailTrace_109401 : CollatzResearch.WordTrace tailWord_109401 prefixEnd_109401 49933597406783734919449 := by
  unfold tailWord_109401
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990182276666336048384057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2660121517777557365589371 3990182276666336048384057)
  ·
    refine ⟨2992636707499752036288043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3990182276666336048384057 2992636707499752036288043)
    ·
      refine ⟨4488955061249628054432065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2992636707499752036288043 4488955061249628054432065)
      ·
        refine ⟨3366716295937221040824049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4488955061249628054432065 3366716295937221040824049)
        ·
          refine ⟨2525037221952915780618037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3366716295937221040824049 2525037221952915780618037)
          ·
            refine ⟨236722239558085854432941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2525037221952915780618037 236722239558085854432941)
            ·
              refine ⟨88770839834282195412353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236722239558085854432941 88770839834282195412353)
              ·
                refine ⟨66578129875711646559265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88770839834282195412353 66578129875711646559265)
                ·
                  refine ⟨49933597406783734919449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66578129875711646559265 49933597406783734919449)
                  ·
                    rfl

theorem cell20_109401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_109401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109401 prefixEnd_109401 := by exact prefixLift 109401
  have htrace : WordTrace (prefixWord ++ tailWord_109401) baseStart_109401 baseEnd_109401 := by
    simpa [prefixWord, tailWord_109401, baseEnd_109401] using wordTrace_append hprefix tailTrace_109401
  have hstable : (prefixWord ++ tailWord_109401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109401).length < 2 ^ (prefixWord ++ tailWord_109401).sum := by decide
  have hdescent : baseEnd_109401 < baseStart_109401 := by decide
  rcases family_descends (prefixWord ++ tailWord_109401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109412 : List Nat := [2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_109412 : Nat := 118140960795 + 109412 * 2 ^ 59
def prefixEnd_109412 : Nat := 4983230072969 + 3 ^ 40 * 109412 * 2
def baseEnd_109412 : Nat := 16646206035505528517579

theorem tailTrace_109412 : CollatzResearch.WordTrace tailWord_109412 prefixEnd_109412 16646206035505528517579 := by
  unfold tailWord_109412
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995291739813242463517245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2660388986417656618022993 1995291739813242463517245)
  ·
    refine ⟨748234402429965923818967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1995291739813242463517245 748234402429965923818967)
    ·
      refine ⟨1122351603644948885728451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 748234402429965923818967 1122351603644948885728451)
      ·
        refine ⟨1683527405467423328592677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122351603644948885728451 1683527405467423328592677)
        ·
          refine ⟨315661388525141874111127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1683527405467423328592677 315661388525141874111127)
          ·
            refine ⟨473492082787712811166691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315661388525141874111127 473492082787712811166691)
            ·
              refine ⟨710238124181569216750037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473492082787712811166691 710238124181569216750037)
              ·
                refine ⟨16646206035505528517579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 710238124181569216750037 16646206035505528517579)
                ·
                  rfl

theorem cell20_109412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_109412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109412 prefixEnd_109412 := by exact prefixLift 109412
  have htrace : WordTrace (prefixWord ++ tailWord_109412) baseStart_109412 baseEnd_109412 := by
    simpa [prefixWord, tailWord_109412, baseEnd_109412] using wordTrace_append hprefix tailTrace_109412
  have hstable : (prefixWord ++ tailWord_109412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109412).length < 2 ^ (prefixWord ++ tailWord_109412).sum := by decide
  have hdescent : baseEnd_109412 < baseStart_109412 := by decide
  rcases family_descends (prefixWord ++ tailWord_109412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109415 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 3]
def baseStart_109415 : Nat := 118140960795 + 109415 * 2 ^ 59
def prefixEnd_109415 : Nat := 4983230072969 + 3 ^ 40 * 109415 * 2
def baseEnd_109415 : Nat := 49939987388261908452725

theorem tailTrace_109415 : CollatzResearch.WordTrace tailWord_109415 prefixEnd_109415 49939987388261908452725 := by
  unfold tailWord_109415
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990692898615616439393699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2660461932410410959595799 3990692898615616439393699)
  ·
    refine ⟨5986039347923424659090549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3990692898615616439393699 5986039347923424659090549)
    ·
      refine ⟨561191188867821061789739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5986039347923424659090549 561191188867821061789739)
      ·
        refine ⟨841786783301731592684609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561191188867821061789739 841786783301731592684609)
        ·
          refine ⟨631340087476298694513457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841786783301731592684609 631340087476298694513457)
          ·
            refine ⟨473505065607224020885093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631340087476298694513457 473505065607224020885093)
            ·
              refine ⟨88782199801354503915955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 473505065607224020885093 88782199801354503915955)
              ·
                refine ⟨133173299702031755873933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88782199801354503915955 133173299702031755873933)
                ·
                  refine ⟨49939987388261908452725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133173299702031755873933 49939987388261908452725)
                  ·
                    rfl

theorem cell20_109415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_109415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109415 prefixEnd_109415 := by exact prefixLift 109415
  have htrace : WordTrace (prefixWord ++ tailWord_109415) baseStart_109415 baseEnd_109415 := by
    simpa [prefixWord, tailWord_109415, baseEnd_109415] using wordTrace_append hprefix tailTrace_109415
  have hstable : (prefixWord ++ tailWord_109415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109415).length < 2 ^ (prefixWord ++ tailWord_109415).sum := by decide
  have hdescent : baseEnd_109415 < baseStart_109415 := by decide
  rcases family_descends (prefixWord ++ tailWord_109415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109450 : List Nat := [3, 1, 2, 4, 1, 9]
def baseStart_109450 : Nat := 118140960795 + 109450 * 2 ^ 59
def prefixEnd_109450 : Nat := 4983230072969 + 3 ^ 40 * 109450 * 2
def baseEnd_109450 : Nat := 1850220827479901566145

theorem tailTrace_109450 : CollatzResearch.WordTrace tailWord_109450 prefixEnd_109450 1850220827479901566145 := by
  unfold tailWord_109450
  simp only [CollatzResearch.WordTrace]
  refine ⟨997992363372204354229451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2661312968992544944611869 997992363372204354229451)
  ·
    refine ⟨1496988545058306531344177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997992363372204354229451 1496988545058306531344177)
    ·
      refine ⟨1122741408793729898508133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496988545058306531344177 1122741408793729898508133)
      ·
        refine ⟨210514014148824355970275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1122741408793729898508133 210514014148824355970275)
        ·
          refine ⟨315771021223236533955413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210514014148824355970275 315771021223236533955413)
          ·
            refine ⟨1850220827479901566145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 315771021223236533955413 1850220827479901566145)
            ·
              rfl

theorem cell20_109450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 9].length) (baseStart_109450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109450 prefixEnd_109450 := by exact prefixLift 109450
  have htrace : WordTrace (prefixWord ++ tailWord_109450) baseStart_109450 baseEnd_109450 := by
    simpa [prefixWord, tailWord_109450, baseEnd_109450] using wordTrace_append hprefix tailTrace_109450
  have hstable : (prefixWord ++ tailWord_109450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109450).length < 2 ^ (prefixWord ++ tailWord_109450).sum := by decide
  have hdescent : baseEnd_109450 < baseStart_109450 := by decide
  rcases family_descends (prefixWord ++ tailWord_109450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109498 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_109498 : Nat := 118140960795 + 109498 * 2 ^ 59
def prefixEnd_109498 : Nat := 4983230072969 + 3 ^ 40 * 109498 * 2
def baseEnd_109498 : Nat := 49977870849882508685719

theorem tailTrace_109498 : CollatzResearch.WordTrace tailWord_109498 prefixEnd_109498 49977870849882508685719 := by
  unfold tailWord_109498
  simp only [CollatzResearch.WordTrace]
  refine ⟨998430039328730403666287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2662480104876614409776765 998430039328730403666287)
  ·
    refine ⟨1497645058993095605499431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998430039328730403666287 1497645058993095605499431)
    ·
      refine ⟨2246467588489643408249147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497645058993095605499431 2246467588489643408249147)
      ·
        refine ⟨3369701382734465112373721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246467588489643408249147 3369701382734465112373721)
        ·
          refine ⟨2527276037050848834280291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369701382734465112373721 2527276037050848834280291)
          ·
            refine ⟨3790914055576273251420437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527276037050848834280291 3790914055576273251420437)
            ·
              refine ⟨177699096355137808660333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3790914055576273251420437 177699096355137808660333)
              ·
                refine ⟨66637161133176678247625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177699096355137808660333 66637161133176678247625)
                ·
                  refine ⟨49977870849882508685719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66637161133176678247625 49977870849882508685719)
                  ·
                    rfl

theorem cell20_109498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_109498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109498 prefixEnd_109498 := by exact prefixLift 109498
  have htrace : WordTrace (prefixWord ++ tailWord_109498) baseStart_109498 baseEnd_109498 := by
    simpa [prefixWord, tailWord_109498, baseEnd_109498] using wordTrace_append hprefix tailTrace_109498
  have hstable : (prefixWord ++ tailWord_109498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109498).length < 2 ^ (prefixWord ++ tailWord_109498).sum := by decide
  have hdescent : baseEnd_109498 < baseStart_109498 := by decide
  rcases family_descends (prefixWord ++ tailWord_109498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109512 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_109512 : Nat := 118140960795 + 109512 * 2 ^ 59
def prefixEnd_109512 : Nat := 4983230072969 + 3 ^ 40 * 109512 * 2
def baseEnd_109512 : Nat := 49984260831360682218995

theorem tailTrace_109512 : CollatzResearch.WordTrace tailWord_109512 prefixEnd_109512 49984260831360682218995 := by
  unfold tailWord_109512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997115389632101002837395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2662820519509468003783193 1997115389632101002837395)
  ·
    refine ⟨2995673084448151504256093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997115389632101002837395 2995673084448151504256093)
    ·
      refine ⟨1123377406668056814096035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2995673084448151504256093 1123377406668056814096035)
      ·
        refine ⟨1685066110002085221144053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123377406668056814096035 1685066110002085221144053)
        ·
          refine ⟨157974947812695489482255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1685066110002085221144053 157974947812695489482255)
          ·
            refine ⟨236962421719043234223383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157974947812695489482255 236962421719043234223383)
            ·
              refine ⟨355443632578564851335075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236962421719043234223383 355443632578564851335075)
              ·
                refine ⟨533165448867847277002613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355443632578564851335075 533165448867847277002613)
                ·
                  refine ⟨49984260831360682218995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 533165448867847277002613 49984260831360682218995)
                  ·
                    rfl

theorem cell20_109512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_109512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109512 prefixEnd_109512 := by exact prefixLift 109512
  have htrace : WordTrace (prefixWord ++ tailWord_109512) baseStart_109512 baseEnd_109512 := by
    simpa [prefixWord, tailWord_109512, baseEnd_109512] using wordTrace_append hprefix tailTrace_109512
  have hstable : (prefixWord ++ tailWord_109512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109512).length < 2 ^ (prefixWord ++ tailWord_109512).sum := by decide
  have hdescent : baseEnd_109512 < baseStart_109512 := by decide
  rcases family_descends (prefixWord ++ tailWord_109512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109519 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_109519 : Nat := 118140960795 + 109519 * 2 ^ 59
def prefixEnd_109519 : Nat := 4983230072969 + 3 ^ 40 * 109519 * 2
def baseEnd_109519 : Nat := 49987455822099768985633

theorem tailTrace_109519 : CollatzResearch.WordTrace tailWord_109519 prefixEnd_109519 49987455822099768985633 := by
  unfold tailWord_109519
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994486090238842201179611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2662990726825894800786407 3994486090238842201179611)
  ·
    refine ⟨5991729135358263301769417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3994486090238842201179611 5991729135358263301769417)
    ·
      refine ⟨4493796851518697476327063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5991729135358263301769417 4493796851518697476327063)
      ·
        refine ⟨6740695277278046214490595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493796851518697476327063 6740695277278046214490595)
        ·
          refine ⟨10111042915917069321735893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740695277278046214490595 10111042915917069321735893)
          ·
            refine ⟨236977568341806312228185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10111042915917069321735893 236977568341806312228185)
            ·
              refine ⟨177733176256354734171139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236977568341806312228185 177733176256354734171139)
              ·
                refine ⟨266599764384532101256709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177733176256354734171139 266599764384532101256709)
                ·
                  refine ⟨49987455822099768985633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266599764384532101256709 49987455822099768985633)
                  ·
                    rfl

theorem cell20_109519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_109519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109519 prefixEnd_109519 := by exact prefixLift 109519
  have htrace : WordTrace (prefixWord ++ tailWord_109519) baseStart_109519 baseEnd_109519 := by
    simpa [prefixWord, tailWord_109519, baseEnd_109519] using wordTrace_append hprefix tailTrace_109519
  have hstable : (prefixWord ++ tailWord_109519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109519).length < 2 ^ (prefixWord ++ tailWord_109519).sum := by decide
  have hdescent : baseEnd_109519 < baseStart_109519 := by decide
  rcases family_descends (prefixWord ++ tailWord_109519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109529 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 3]
def baseStart_109529 : Nat := 118140960795 + 109529 * 2 ^ 59
def prefixEnd_109529 : Nat := 4983230072969 + 3 ^ 40 * 109529 * 2
def baseEnd_109529 : Nat := 49992020094584178652259

theorem tailTrace_109529 : CollatzResearch.WordTrace tailWord_109529 prefixEnd_109529 49992020094584178652259 := by
  unfold tailWord_109529
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994850820202613909043641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2663233880135075939362427 3994850820202613909043641)
  ·
    refine ⟨2996138115151960431782731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3994850820202613909043641 2996138115151960431782731)
    ·
      refine ⟨4494207172727940647674097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2996138115151960431782731 4494207172727940647674097)
      ·
        refine ⟨3370655379545955485755573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4494207172727940647674097 3370655379545955485755573)
        ·
          refine ⟨315998941832433326789585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3370655379545955485755573 315998941832433326789585)
          ·
            refine ⟨236999206374324995092189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315998941832433326789585 236999206374324995092189)
            ·
              refine ⟨88874702390371873159571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236999206374324995092189 88874702390371873159571)
              ·
                refine ⟨133312053585557809739357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88874702390371873159571 133312053585557809739357)
                ·
                  refine ⟨49992020094584178652259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133312053585557809739357 49992020094584178652259)
                  ·
                    rfl

theorem cell20_109529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_109529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109529 prefixEnd_109529 := by exact prefixLift 109529
  have htrace : WordTrace (prefixWord ++ tailWord_109529) baseStart_109529 baseEnd_109529 := by
    simpa [prefixWord, tailWord_109529, baseEnd_109529] using wordTrace_append hprefix tailTrace_109529
  have hstable : (prefixWord ++ tailWord_109529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109529).length < 2 ^ (prefixWord ++ tailWord_109529).sum := by decide
  have hdescent : baseEnd_109529 < baseStart_109529 := by decide
  rcases family_descends (prefixWord ++ tailWord_109529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109540 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_109540 : Nat := 118140960795 + 109540 * 2 ^ 59
def prefixEnd_109540 : Nat := 4983230072969 + 3 ^ 40 * 109540 * 2
def baseEnd_109540 : Nat := 49997040794317029285547

theorem tailTrace_109540 : CollatzResearch.WordTrace tailWord_109540 prefixEnd_109540 49997040794317029285547 := by
  unfold tailWord_109540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997626011581381393847037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2663501348775175191796049 1997626011581381393847037)
  ·
    refine ⟨749109754343018022692639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1997626011581381393847037 749109754343018022692639)
    ·
      refine ⟨1123664631514527034038959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749109754343018022692639 1123664631514527034038959)
      ·
        refine ⟨1685496947271790551058439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123664631514527034038959 1685496947271790551058439)
        ·
          refine ⟨2528245420907685826587659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685496947271790551058439 2528245420907685826587659)
          ·
            refine ⟨3792368131361528739881489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528245420907685826587659 3792368131361528739881489)
            ·
              refine ⟨2844276098521146554911117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792368131361528739881489 2844276098521146554911117)
              ·
                refine ⟨1066603536945429958091669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2844276098521146554911117 1066603536945429958091669)
                ·
                  refine ⟨49997040794317029285547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1066603536945429958091669 49997040794317029285547)
                  ·
                    rfl

theorem cell20_109540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_109540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109540 prefixEnd_109540 := by exact prefixLift 109540
  have htrace : WordTrace (prefixWord ++ tailWord_109540) baseStart_109540 baseEnd_109540 := by
    simpa [prefixWord, tailWord_109540, baseEnd_109540] using wordTrace_append hprefix tailTrace_109540
  have hstable : (prefixWord ++ tailWord_109540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109540).length < 2 ^ (prefixWord ++ tailWord_109540).sum := by decide
  have hdescent : baseEnd_109540 < baseStart_109540 := by decide
  rcases family_descends (prefixWord ++ tailWord_109540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109543 : List Nat := [1, 1, 5, 2, 2, 1, 4, 4]
def baseStart_109543 : Nat := 118140960795 + 109543 * 2 ^ 59
def prefixEnd_109543 : Nat := 4983230072969 + 3 ^ 40 * 109543 * 2
def baseEnd_109543 : Nat := 16666136692020784061845

theorem tailTrace_109543 : CollatzResearch.WordTrace tailWord_109543 prefixEnd_109543 16666136692020784061845 := by
  unfold tailWord_109543
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995361442151894300053283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2663574294767929533368855 3995361442151894300053283)
  ·
    refine ⟨5993042163227841450079925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995361442151894300053283 5993042163227841450079925)
    ·
      refine ⟨561847702802610135944993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5993042163227841450079925 561847702802610135944993)
      ·
        refine ⟨421385777101957601958745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561847702802610135944993 421385777101957601958745)
        ·
          refine ⟨316039332826468201469059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421385777101957601958745 316039332826468201469059)
          ·
            refine ⟨474058999239702302203589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316039332826468201469059 474058999239702302203589)
            ·
              refine ⟨88886062357444181663173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 474058999239702302203589 88886062357444181663173)
              ·
                refine ⟨16666136692020784061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88886062357444181663173 16666136692020784061845)
                ·
                  rfl

theorem cell20_109543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_109543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109543 prefixEnd_109543 := by exact prefixLift 109543
  have htrace : WordTrace (prefixWord ++ tailWord_109543) baseStart_109543 baseEnd_109543 := by
    simpa [prefixWord, tailWord_109543, baseEnd_109543] using wordTrace_append hprefix tailTrace_109543
  have hstable : (prefixWord ++ tailWord_109543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109543).length < 2 ^ (prefixWord ++ tailWord_109543).sum := by decide
  have hdescent : baseEnd_109543 < baseStart_109543 := by decide
  rcases family_descends (prefixWord ++ tailWord_109543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109553 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 2]
def baseStart_109553 : Nat := 118140960795 + 109553 * 2 ^ 59
def prefixEnd_109553 : Nat := 4983230072969 + 3 ^ 40 * 109553 * 2
def baseEnd_109553 : Nat := 50002974348546761852161

theorem tailTrace_109553 : CollatzResearch.WordTrace tailWord_109553 prefixEnd_109553 50002974348546761852161 := by
  unfold tailWord_109553
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995726172115666007917313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2663817448077110671944875 3995726172115666007917313)
  ·
    refine ⟨2996794629086749505937985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3995726172115666007917313 2996794629086749505937985)
    ·
      refine ⟨2247595971815062129453489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996794629086749505937985 2247595971815062129453489)
      ·
        refine ⟨1685696978861296597090117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247595971815062129453489 1685696978861296597090117)
        ·
          refine ⟨316068183536493111954397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1685696978861296597090117 316068183536493111954397)
          ·
            refine ⟨118525568826184916982899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316068183536493111954397 118525568826184916982899)
            ·
              refine ⟨177788353239277375474349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118525568826184916982899 177788353239277375474349)
              ·
                refine ⟨66670632464729015802881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177788353239277375474349 66670632464729015802881)
                ·
                  refine ⟨50002974348546761852161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66670632464729015802881 50002974348546761852161)
                  ·
                    rfl

theorem cell20_109553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_109553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109553 prefixEnd_109553 := by exact prefixLift 109553
  have htrace : WordTrace (prefixWord ++ tailWord_109553) baseStart_109553 baseEnd_109553 := by
    simpa [prefixWord, tailWord_109553, baseEnd_109553] using wordTrace_append hprefix tailTrace_109553
  have hstable : (prefixWord ++ tailWord_109553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109553).length < 2 ^ (prefixWord ++ tailWord_109553).sum := by decide
  have hdescent : baseEnd_109553 < baseStart_109553 := by decide
  rcases family_descends (prefixWord ++ tailWord_109553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109556 : List Nat := [2, 6, 2, 1, 1, 2, 6]
def baseStart_109556 : Nat := 118140960795 + 109556 * 2 ^ 59
def prefixEnd_109556 : Nat := 4983230072969 + 3 ^ 40 * 109556 * 2
def baseEnd_109556 : Nat := 5556038181143564972461

theorem tailTrace_109556 : CollatzResearch.WordTrace tailWord_109556 prefixEnd_109556 5556038181143564972461 := by
  unfold tailWord_109556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997917795552398760138261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2663890394069865013517681 1997917795552398760138261)
  ·
    refine ⟨93652396666518691881481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1997917795552398760138261 93652396666518691881481)
    ·
      refine ⟨70239297499889018911111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93652396666518691881481 70239297499889018911111)
      ·
        refine ⟨105358946249833528366667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70239297499889018911111 105358946249833528366667)
        ·
          refine ⟨158038419374750292550001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105358946249833528366667 158038419374750292550001)
          ·
            refine ⟨118528814531062719412501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158038419374750292550001 118528814531062719412501)
            ·
              refine ⟨5556038181143564972461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118528814531062719412501 5556038181143564972461)
              ·
                rfl

theorem cell20_109556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 6].length) (baseStart_109556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109556 prefixEnd_109556 := by exact prefixLift 109556
  have htrace : WordTrace (prefixWord ++ tailWord_109556) baseStart_109556 baseEnd_109556 := by
    simpa [prefixWord, tailWord_109556, baseEnd_109556] using wordTrace_append hprefix tailTrace_109556
  have hstable : (prefixWord ++ tailWord_109556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109556).length < 2 ^ (prefixWord ++ tailWord_109556).sum := by decide
  have hdescent : baseEnd_109556 < baseStart_109556 := by decide
  rcases family_descends (prefixWord ++ tailWord_109556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109564 : List Nat := [2, 2, 2, 1, 2, 5, 6]
def baseStart_109564 : Nat := 118140960795 + 109564 * 2 ^ 59
def prefixEnd_109564 : Nat := 4983230072969 + 3 ^ 40 * 109564 * 2
def baseEnd_109564 : Nat := 5556443894253290276161

theorem tailTrace_109564 : CollatzResearch.WordTrace tailWord_109564 prefixEnd_109564 5556443894253290276161 := by
  unfold tailWord_109564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998063687537907443283873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2664084916717209924378497 1998063687537907443283873)
  ·
    refine ⟨1498547765653430582462905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1998063687537907443283873 1498547765653430582462905)
    ·
      refine ⟨1123910824240072936847179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1498547765653430582462905 1123910824240072936847179)
      ·
        refine ⟨1685866236360109405270769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123910824240072936847179 1685866236360109405270769)
        ·
          refine ⟨1264399677270082053953077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685866236360109405270769 1264399677270082053953077)
          ·
            refine ⟨118537469744070192558101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1264399677270082053953077 118537469744070192558101)
            ·
              refine ⟨5556443894253290276161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118537469744070192558101 5556443894253290276161)
              ·
                rfl

theorem cell20_109564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 6].length) (baseStart_109564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109564 prefixEnd_109564 := by exact prefixLift 109564
  have htrace : WordTrace (prefixWord ++ tailWord_109564) baseStart_109564 baseEnd_109564 := by
    simpa [prefixWord, tailWord_109564, baseEnd_109564] using wordTrace_append hprefix tailTrace_109564
  have hstable : (prefixWord ++ tailWord_109564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109564).length < 2 ^ (prefixWord ++ tailWord_109564).sum := by decide
  have hdescent : baseEnd_109564 < baseStart_109564 := by decide
  rcases family_descends (prefixWord ++ tailWord_109564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109570 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_109570 : Nat := 118140960795 + 109570 * 2 ^ 59
def prefixEnd_109570 : Nat := 4983230072969 + 3 ^ 40 * 109570 * 2
def baseEnd_109570 : Nat := 50010733611770258285425

theorem tailTrace_109570 : CollatzResearch.WordTrace tailWord_109570 prefixEnd_109570 50010733611770258285425 := by
  unfold tailWord_109570
  simp only [CollatzResearch.WordTrace]
  refine ⟨999086553263519477821541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2664230808702718607524109 999086553263519477821541)
  ·
    refine ⟨187328728736909902091539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 999086553263519477821541 187328728736909902091539)
    ·
      refine ⟨280993093105364853137309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187328728736909902091539 280993093105364853137309)
      ·
        refine ⟨105372409914511819926491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280993093105364853137309 105372409914511819926491)
        ·
          refine ⟨158058614871767729889737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105372409914511819926491 158058614871767729889737)
          ·
            refine ⟨118543961153825797417303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158058614871767729889737 118543961153825797417303)
            ·
              refine ⟨177815941730738696125955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118543961153825797417303 177815941730738696125955)
              ·
                refine ⟨266723912596108044188933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177815941730738696125955 266723912596108044188933)
                ·
                  refine ⟨50010733611770258285425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266723912596108044188933 50010733611770258285425)
                  ·
                    rfl

theorem cell20_109570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_109570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109570 prefixEnd_109570 := by exact prefixLift 109570
  have htrace : WordTrace (prefixWord ++ tailWord_109570) baseStart_109570 baseEnd_109570 := by
    simpa [prefixWord, tailWord_109570, baseEnd_109570] using wordTrace_append hprefix tailTrace_109570
  have hstable : (prefixWord ++ tailWord_109570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109570).length < 2 ^ (prefixWord ++ tailWord_109570).sum := by decide
  have hdescent : baseEnd_109570 < baseStart_109570 := by decide
  rcases family_descends (prefixWord ++ tailWord_109570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109602 : List Nat := [3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_109602 : Nat := 118140960795 + 109602 * 2 ^ 59
def prefixEnd_109602 : Nat := 4983230072969 + 3 ^ 40 * 109602 * 2
def baseEnd_109602 : Nat := 16675113094573456406209

theorem tailTrace_109602 : CollatzResearch.WordTrace tailWord_109602 prefixEnd_109602 16675113094573456406209 := by
  unfold tailWord_109602
  simp only [CollatzResearch.WordTrace]
  refine ⟨999378337234536844112765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2665008899292098250967373 999378337234536844112765)
  ·
    refine ⟨374766876462951316542287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 999378337234536844112765 374766876462951316542287)
    ·
      refine ⟨562150314694426974813431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374766876462951316542287 562150314694426974813431)
      ·
        refine ⟨843225472041640462220147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562150314694426974813431 843225472041640462220147)
        ·
          refine ⟨1264838208062460693330221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843225472041640462220147 1264838208062460693330221)
          ·
            refine ⟨474314328023422759998833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1264838208062460693330221 474314328023422759998833)
            ·
              refine ⟨355735746017567069999125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474314328023422759998833 355735746017567069999125)
              ·
                refine ⟨16675113094573456406209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355735746017567069999125 16675113094573456406209)
                ·
                  rfl

theorem cell20_109602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_109602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109602 prefixEnd_109602 := by exact prefixLift 109602
  have htrace : WordTrace (prefixWord ++ tailWord_109602) baseStart_109602 baseEnd_109602 := by
    simpa [prefixWord, tailWord_109602, baseEnd_109602] using wordTrace_append hprefix tailTrace_109602
  have hstable : (prefixWord ++ tailWord_109602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109602).length < 2 ^ (prefixWord ++ tailWord_109602).sum := by decide
  have hdescent : baseEnd_109602 < baseStart_109602 := by decide
  rcases family_descends (prefixWord ++ tailWord_109602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109629 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 2]
def baseStart_109629 : Nat := 118140960795 + 109629 * 2 ^ 59
def prefixEnd_109629 : Nat := 4983230072969 + 3 ^ 40 * 109629 * 2
def baseEnd_109629 : Nat := 50037662819428275318517

theorem tailTrace_109629 : CollatzResearch.WordTrace tailWord_109629 prefixEnd_109629 50037662819428275318517 := by
  unfold tailWord_109629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998498119840330987683941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2665665413226887325122627 3998498119840330987683941)
  ·
    refine ⟨749718397470062060190739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3998498119840330987683941 749718397470062060190739)
    ·
      refine ⟨1124577596205093090286109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749718397470062060190739 1124577596205093090286109)
      ·
        refine ⟨421716598576909908857291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1124577596205093090286109 421716598576909908857291)
        ·
          refine ⟨632574897865364863285937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421716598576909908857291 632574897865364863285937)
          ·
            refine ⟨474431173399023647464453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632574897865364863285937 474431173399023647464453)
            ·
              refine ⟨88955845012316933899585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 474431173399023647464453 88955845012316933899585)
              ·
                refine ⟨66716883759237700424689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88955845012316933899585 66716883759237700424689)
                ·
                  refine ⟨50037662819428275318517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66716883759237700424689 50037662819428275318517)
                  ·
                    rfl

theorem cell20_109629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_109629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109629 prefixEnd_109629 := by exact prefixLift 109629
  have htrace : WordTrace (prefixWord ++ tailWord_109629) baseStart_109629 baseEnd_109629 := by
    simpa [prefixWord, tailWord_109629, baseEnd_109629] using wordTrace_append hprefix tailTrace_109629
  have hstable : (prefixWord ++ tailWord_109629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109629).length < 2 ^ (prefixWord ++ tailWord_109629).sum := by decide
  have hdescent : baseEnd_109629 < baseStart_109629 := by decide
  rcases family_descends (prefixWord ++ tailWord_109629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109678 : List Nat := [4, 1, 2, 2, 1, 3, 7]
def baseStart_109678 : Nat := 118140960795 + 109678 * 2 ^ 59
def prefixEnd_109678 : Nat := 4983230072969 + 3 ^ 40 * 109678 * 2
def baseEnd_109678 : Nat := 5562225306066875853887

theorem tailTrace_109678 : CollatzResearch.WordTrace tailWord_109678 prefixEnd_109678 5562225306066875853887 := by
  unfold tailWord_109678
  simp only [CollatzResearch.WordTrace]
  refine ⟨500035662082851544527211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2666856864441874904145125 500035662082851544527211)
  ·
    refine ⟨750053493124277316790817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 500035662082851544527211 750053493124277316790817)
    ·
      refine ⟨562540119843207987593113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 750053493124277316790817 562540119843207987593113)
      ·
        refine ⟨421905089882405990694835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562540119843207987593113 421905089882405990694835)
        ·
          refine ⟨632857634823608986042253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421905089882405990694835 632857634823608986042253)
          ·
            refine ⟨237321613058853369765845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632857634823608986042253 237321613058853369765845)
            ·
              refine ⟨5562225306066875853887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 237321613058853369765845 5562225306066875853887)
              ·
                rfl

theorem cell20_109678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_109678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109678 prefixEnd_109678 := by exact prefixLift 109678
  have htrace : WordTrace (prefixWord ++ tailWord_109678) baseStart_109678 baseEnd_109678 := by
    simpa [prefixWord, tailWord_109678, baseEnd_109678] using wordTrace_append hprefix tailTrace_109678
  have hstable : (prefixWord ++ tailWord_109678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109678).length < 2 ^ (prefixWord ++ tailWord_109678).sum := by decide
  have hdescent : baseEnd_109678 < baseStart_109678 := by decide
  rcases family_descends (prefixWord ++ tailWord_109678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109694 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_109694 : Nat := 118140960795 + 109694 * 2 ^ 59
def prefixEnd_109694 : Nat := 4983230072969 + 3 ^ 40 * 109694 * 2
def baseEnd_109694 : Nat := 50067330590576938151585

theorem tailTrace_109694 : CollatzResearch.WordTrace tailWord_109694 prefixEnd_109694 50067330590576938151585 := by
  unfold tailWord_109694
  simp only [CollatzResearch.WordTrace]
  refine ⟨500108608075605886100017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2667245909736564725866757 500108608075605886100017)
  ·
    refine ⟨375081456056704414575013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 500108608075605886100017 375081456056704414575013)
    ·
      refine ⟨70327773010632077732815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375081456056704414575013 70327773010632077732815)
      ·
        refine ⟨105491659515948116599223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70327773010632077732815 105491659515948116599223)
        ·
          refine ⟨158237489273922174898835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105491659515948116599223 158237489273922174898835)
          ·
            refine ⟨237356233910883262348253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158237489273922174898835 237356233910883262348253)
            ·
              refine ⟨89008587716581223380595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237356233910883262348253 89008587716581223380595)
              ·
                refine ⟨133512881574871835070893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89008587716581223380595 133512881574871835070893)
                ·
                  refine ⟨50067330590576938151585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133512881574871835070893 50067330590576938151585)
                  ·
                    rfl

theorem cell20_109694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_109694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109694 prefixEnd_109694 := by exact prefixLift 109694
  have htrace : WordTrace (prefixWord ++ tailWord_109694) baseStart_109694 baseEnd_109694 := by
    simpa [prefixWord, tailWord_109694, baseEnd_109694] using wordTrace_append hprefix tailTrace_109694
  have hstable : (prefixWord ++ tailWord_109694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109694).length < 2 ^ (prefixWord ++ tailWord_109694).sum := by decide
  have hdescent : baseEnd_109694 < baseStart_109694 := by decide
  rcases family_descends (prefixWord ++ tailWord_109694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109699 : List Nat := [1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_109699 : Nat := 118140960795 + 109699 * 2 ^ 59
def prefixEnd_109699 : Nat := 4983230072969 + 3 ^ 40 * 109699 * 2
def baseEnd_109699 : Nat := 16689870908939714328299

theorem tailTrace_109699 : CollatzResearch.WordTrace tailWord_109699 prefixEnd_109699 16689870908939714328299 := by
  unfold tailWord_109699
  simp only [CollatzResearch.WordTrace]
  refine ⟨4001051229586732942732151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2667367486391155295154767 4001051229586732942732151)
  ·
    refine ⟨6001576844380099414098227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4001051229586732942732151 6001576844380099414098227)
    ·
      refine ⟨9002365266570149121147341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001576844380099414098227 9002365266570149121147341)
      ·
        refine ⟨3375886974963805920430253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9002365266570149121147341 3375886974963805920430253)
        ·
          refine ⟨1265957615611427220161345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3375886974963805920430253 1265957615611427220161345)
          ·
            refine ⟨949468211708570415121009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265957615611427220161345 949468211708570415121009)
            ·
              refine ⟨712101158781427811340757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949468211708570415121009 712101158781427811340757)
              ·
                refine ⟨16689870908939714328299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 712101158781427811340757 16689870908939714328299)
                ·
                  rfl

theorem cell20_109699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_109699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109699 prefixEnd_109699 := by exact prefixLift 109699
  have htrace : WordTrace (prefixWord ++ tailWord_109699) baseStart_109699 baseEnd_109699 := by
    simpa [prefixWord, tailWord_109699, baseEnd_109699] using wordTrace_append hprefix tailTrace_109699
  have hstable : (prefixWord ++ tailWord_109699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109699).length < 2 ^ (prefixWord ++ tailWord_109699).sum := by decide
  have hdescent : baseEnd_109699 < baseStart_109699 := by decide
  rcases family_descends (prefixWord ++ tailWord_109699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109747 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 2]
def baseStart_109747 : Nat := 118140960795 + 109747 * 2 ^ 59
def prefixEnd_109747 : Nat := 4983230072969 + 3 ^ 40 * 109747 * 2
def baseEnd_109747 : Nat := 50091521234744309384701

theorem tailTrace_109747 : CollatzResearch.WordTrace tailWord_109747 prefixEnd_109747 50091521234744309384701 := by
  unfold tailWord_109747
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002801933412837140479495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668534622275224760319663 4002801933412837140479495)
  ·
    refine ⟨6004202900119255710719243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4002801933412837140479495 6004202900119255710719243)
    ·
      refine ⟨9006304350178883566078865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6004202900119255710719243 9006304350178883566078865)
      ·
        refine ⟨6754728262634162674559149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9006304350178883566078865 6754728262634162674559149)
        ·
          refine ⟨2533023098487811002959681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6754728262634162674559149 2533023098487811002959681)
          ·
            refine ⟨1899767323865858252219761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533023098487811002959681 1899767323865858252219761)
            ·
              refine ⟨1424825492899393689164821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899767323865858252219761 1424825492899393689164821)
              ·
                refine ⟨66788694979659079179601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1424825492899393689164821 66788694979659079179601)
                ·
                  refine ⟨50091521234744309384701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66788694979659079179601 50091521234744309384701)
                  ·
                    rfl

theorem cell20_109747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 2].length) (baseStart_109747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109747 prefixEnd_109747 := by exact prefixLift 109747
  have htrace : WordTrace (prefixWord ++ tailWord_109747) baseStart_109747 baseEnd_109747 := by
    simpa [prefixWord, tailWord_109747, baseEnd_109747] using wordTrace_append hprefix tailTrace_109747
  have hstable : (prefixWord ++ tailWord_109747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109747).length < 2 ^ (prefixWord ++ tailWord_109747).sum := by decide
  have hdescent : baseEnd_109747 < baseStart_109747 := by decide
  rcases family_descends (prefixWord ++ tailWord_109747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109768 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_109768 : Nat := 118140960795 + 109768 * 2 ^ 59
def prefixEnd_109768 : Nat := 4983230072969 + 3 ^ 40 * 109768 * 2
def baseEnd_109768 : Nat := 50101106206961569684615

theorem tailTrace_109768 : CollatzResearch.WordTrace tailWord_109768 prefixEnd_109768 50101106206961569684615 := by
  unfold tailWord_109768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001783933168378863496979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2669045244224505151329305 2001783933168378863496979)
  ·
    refine ⟨3002675899752568295245469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001783933168378863496979 3002675899752568295245469)
    ·
      refine ⟨1126003462407213110717051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3002675899752568295245469 1126003462407213110717051)
      ·
        refine ⟨1689005193610819666075577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126003462407213110717051 1689005193610819666075577)
        ·
          refine ⟨1266753895208114749556683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1689005193610819666075577 1266753895208114749556683)
          ·
            refine ⟨1900130842812172124335025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266753895208114749556683 1900130842812172124335025)
            ·
              refine ⟨1425098132109129093251269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900130842812172124335025 1425098132109129093251269)
              ·
                refine ⟨267205899770461704984613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1425098132109129093251269 267205899770461704984613)
                ·
                  refine ⟨50101106206961569684615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267205899770461704984613 50101106206961569684615)
                  ·
                    rfl

theorem cell20_109768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_109768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109768 prefixEnd_109768 := by exact prefixLift 109768
  have htrace : WordTrace (prefixWord ++ tailWord_109768) baseStart_109768 baseEnd_109768 := by
    simpa [prefixWord, tailWord_109768, baseEnd_109768] using wordTrace_append hprefix tailTrace_109768
  have hstable : (prefixWord ++ tailWord_109768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109768).length < 2 ^ (prefixWord ++ tailWord_109768).sum := by decide
  have hdescent : baseEnd_109768 < baseStart_109768 := by decide
  rcases family_descends (prefixWord ++ tailWord_109768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109785 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 2]
def baseStart_109785 : Nat := 118140960795 + 109785 * 2 ^ 59
def prefixEnd_109785 : Nat := 4983230072969 + 3 ^ 40 * 109785 * 2
def baseEnd_109785 : Nat := 50108865470185066117879

theorem tailTrace_109785 : CollatzResearch.WordTrace tailWord_109785 prefixEnd_109785 50108865470185066117879 := by
  unfold tailWord_109785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004187907275169630362809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2669458604850113086908539 4004187907275169630362809)
  ·
    refine ⟨3003140930456377222772107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4004187907275169630362809 3003140930456377222772107)
    ·
      refine ⟨4504711395684565834158161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3003140930456377222772107 4504711395684565834158161)
      ·
        refine ⟨3378533546763424375618621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504711395684565834158161 3378533546763424375618621)
        ·
          refine ⟨1266950080036284140856983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3378533546763424375618621 1266950080036284140856983)
          ·
            refine ⟨1900425120054426211285475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266950080036284140856983 1900425120054426211285475)
            ·
              refine ⟨2850637680081639316928213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900425120054426211285475 2850637680081639316928213)
              ·
                refine ⟨66811820626913421490505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2850637680081639316928213 66811820626913421490505)
                ·
                  refine ⟨50108865470185066117879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66811820626913421490505 50108865470185066117879)
                  ·
                    rfl

theorem cell20_109785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_109785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109785 prefixEnd_109785 := by exact prefixLift 109785
  have htrace : WordTrace (prefixWord ++ tailWord_109785) baseStart_109785 baseEnd_109785 := by
    simpa [prefixWord, tailWord_109785, baseEnd_109785] using wordTrace_append hprefix tailTrace_109785
  have hstable : (prefixWord ++ tailWord_109785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109785).length < 2 ^ (prefixWord ++ tailWord_109785).sum := by decide
  have hdescent : baseEnd_109785 < baseStart_109785 := by decide
  rcases family_descends (prefixWord ++ tailWord_109785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109802 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_109802 : Nat := 118140960795 + 109802 * 2 ^ 59
def prefixEnd_109802 : Nat := 4983230072969 + 3 ^ 40 * 109802 * 2
def baseEnd_109802 : Nat := 50116624733408562551143

theorem tailTrace_109802 : CollatzResearch.WordTrace tailWord_109802 prefixEnd_109802 50116624733408562551143 := by
  unfold tailWord_109802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001201987053395383432915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2669871965475721022487773 1001201987053395383432915)
  ·
    refine ⟨1501802980580093075149373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001201987053395383432915 1501802980580093075149373)
    ·
      refine ⟨563176117717534903181015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1501802980580093075149373 563176117717534903181015)
      ·
        refine ⟨844764176576302354771523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563176117717534903181015 844764176576302354771523)
        ·
          refine ⟨1267146264864453532157285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844764176576302354771523 1267146264864453532157285)
          ·
            refine ⟨237589924662085037279491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1267146264864453532157285 237589924662085037279491)
            ·
              refine ⟨356384886993127555919237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237589924662085037279491 356384886993127555919237)
              ·
                refine ⟨66822166311211416734857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 356384886993127555919237 66822166311211416734857)
                ·
                  refine ⟨50116624733408562551143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66822166311211416734857 50116624733408562551143)
                  ·
                    rfl

theorem cell20_109802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_109802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109802 prefixEnd_109802 := by exact prefixLift 109802
  have htrace : WordTrace (prefixWord ++ tailWord_109802) baseStart_109802 baseEnd_109802 := by
    simpa [prefixWord, tailWord_109802, baseEnd_109802] using wordTrace_append hprefix tailTrace_109802
  have hstable : (prefixWord ++ tailWord_109802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109802).length < 2 ^ (prefixWord ++ tailWord_109802).sum := by decide
  have hdescent : baseEnd_109802 < baseStart_109802 := by decide
  rcases family_descends (prefixWord ++ tailWord_109802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109826 : List Nat := [3, 4, 1, 1, 3, 1, 3, 4]
def baseStart_109826 : Nat := 118140960795 + 109826 * 2 ^ 59
def prefixEnd_109826 : Nat := 4983230072969 + 3 ^ 40 * 109826 * 2
def baseEnd_109826 : Nat := 16709192995790381917015

theorem tailTrace_109826 : CollatzResearch.WordTrace tailWord_109826 prefixEnd_109826 16709192995790381917015 := by
  unfold tailWord_109826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001420825031658408151333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2670455533417755755070221 1001420825031658408151333)
  ·
    refine ⟨187766404693435951528375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1001420825031658408151333 187766404693435951528375)
    ·
      refine ⟨281649607040153927292563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187766404693435951528375 281649607040153927292563)
      ·
        refine ⟨422474410560230890938845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281649607040153927292563 422474410560230890938845)
        ·
          refine ⟨158427903960086584102067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422474410560230890938845 158427903960086584102067)
          ·
            refine ⟨237641855940129876153101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158427903960086584102067 237641855940129876153101)
            ·
              refine ⟨89115695977548703557413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237641855940129876153101 89115695977548703557413)
              ·
                refine ⟨16709192995790381917015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89115695977548703557413 16709192995790381917015)
                ·
                  rfl

theorem cell20_109826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_109826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109826 prefixEnd_109826 := by exact prefixLift 109826
  have htrace : WordTrace (prefixWord ++ tailWord_109826) baseStart_109826 baseEnd_109826 := by
    simpa [prefixWord, tailWord_109826, baseEnd_109826] using wordTrace_append hprefix tailTrace_109826
  have hstable : (prefixWord ++ tailWord_109826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109826).length < 2 ^ (prefixWord ++ tailWord_109826).sum := by decide
  have hdescent : baseEnd_109826 < baseStart_109826 := by decide
  rcases family_descends (prefixWord ++ tailWord_109826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109861 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_109861 : Nat := 118140960795 + 109861 * 2 ^ 59
def prefixEnd_109861 : Nat := 4983230072969 + 3 ^ 40 * 109861 * 2
def baseEnd_109861 : Nat := 50143553941066579584235

theorem tailTrace_109861 : CollatzResearch.WordTrace tailWord_109861 prefixEnd_109861 50143553941066579584235 := by
  unfold tailWord_109861
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006959854999834610129437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2671306569999889740086291 4006959854999834610129437)
  ·
    refine ⟨1502609945624937978798539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4006959854999834610129437 1502609945624937978798539)
    ·
      refine ⟨2253914918437406968197809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502609945624937978798539 2253914918437406968197809)
      ·
        refine ⟨1690436188828055226148357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253914918437406968197809 1690436188828055226148357)
        ·
          refine ⟨316956785405260354902817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1690436188828055226148357 316956785405260354902817)
          ·
            refine ⟨237717589053945266177113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316956785405260354902817 237717589053945266177113)
            ·
              refine ⟨178288191790458949632835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237717589053945266177113 178288191790458949632835)
              ·
                refine ⟨267432287685688424449253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178288191790458949632835 267432287685688424449253)
                ·
                  refine ⟨50143553941066579584235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267432287685688424449253 50143553941066579584235)
                  ·
                    rfl

theorem cell20_109861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_109861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109861 prefixEnd_109861 := by exact prefixLift 109861
  have htrace : WordTrace (prefixWord ++ tailWord_109861) baseStart_109861 baseEnd_109861 := by
    simpa [prefixWord, tailWord_109861, baseEnd_109861] using wordTrace_append hprefix tailTrace_109861
  have hstable : (prefixWord ++ tailWord_109861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109861).length < 2 ^ (prefixWord ++ tailWord_109861).sum := by decide
  have hdescent : baseEnd_109861 < baseStart_109861 := by decide
  rcases family_descends (prefixWord ++ tailWord_109861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109882 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_109882 : Nat := 118140960795 + 109882 * 2 ^ 59
def prefixEnd_109882 : Nat := 4983230072969 + 3 ^ 40 * 109882 * 2
def baseEnd_109882 : Nat := 50153138913283839884149

theorem tailTrace_109882 : CollatzResearch.WordTrace tailWord_109882 prefixEnd_109882 50153138913283839884149 := by
  unfold tailWord_109882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001931446980938799160975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2671817191949170131095933 1001931446980938799160975)
  ·
    refine ⟨1502897170471408198741463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001931446980938799160975 1502897170471408198741463)
    ·
      refine ⟨2254345755707112298112195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502897170471408198741463 2254345755707112298112195)
      ·
        refine ⟨3381518633560668447168293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254345755707112298112195 3381518633560668447168293)
        ·
          refine ⟨634034743792625333844055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3381518633560668447168293 634034743792625333844055)
          ·
            refine ⟨951052115688938000766083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634034743792625333844055 951052115688938000766083)
            ·
              refine ⟨1426578173533407001149125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951052115688938000766083 1426578173533407001149125)
              ·
                refine ⟨267483407537513812715461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1426578173533407001149125 267483407537513812715461)
                ·
                  refine ⟨50153138913283839884149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267483407537513812715461 50153138913283839884149)
                  ·
                    rfl

theorem cell20_109882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_109882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109882 prefixEnd_109882 := by exact prefixLift 109882
  have htrace : WordTrace (prefixWord ++ tailWord_109882) baseStart_109882 baseEnd_109882 := by
    simpa [prefixWord, tailWord_109882, baseEnd_109882] using wordTrace_append hprefix tailTrace_109882
  have hstable : (prefixWord ++ tailWord_109882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109882).length < 2 ^ (prefixWord ++ tailWord_109882).sum := by decide
  have hdescent : baseEnd_109882 < baseStart_109882 := by decide
  rcases family_descends (prefixWord ++ tailWord_109882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109885 : List Nat := [1, 4, 1, 5, 1, 1, 1, 6]
def baseStart_109885 : Nat := 118140960795 + 109885 * 2 ^ 59
def prefixEnd_109885 : Nat := 4983230072969 + 3 ^ 40 * 109885 * 2
def baseEnd_109885 : Nat := 16718169398343054261379

theorem tailTrace_109885 : CollatzResearch.WordTrace tailWord_109885 prefixEnd_109885 16718169398343054261379 := by
  unfold tailWord_109885
  simp only [CollatzResearch.WordTrace]
  refine ⟨4007835206912886709003109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2671890137941924472668739 4007835206912886709003109)
  ·
    refine ⟨751469101296166257938083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4007835206912886709003109 751469101296166257938083)
    ·
      refine ⟨1127203651944249386907125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751469101296166257938083 1127203651944249386907125)
      ·
        refine ⟨105675342369773380022543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1127203651944249386907125 105675342369773380022543)
        ·
          refine ⟨158513013554660070033815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105675342369773380022543 158513013554660070033815)
          ·
            refine ⟨237769520331990105050723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158513013554660070033815 237769520331990105050723)
            ·
              refine ⟨356654280497985157576085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237769520331990105050723 356654280497985157576085)
              ·
                refine ⟨16718169398343054261379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 356654280497985157576085 16718169398343054261379)
                ·
                  rfl

theorem cell20_109885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_109885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109885 prefixEnd_109885 := by exact prefixLift 109885
  have htrace : WordTrace (prefixWord ++ tailWord_109885) baseStart_109885 baseEnd_109885 := by
    simpa [prefixWord, tailWord_109885, baseEnd_109885] using wordTrace_append hprefix tailTrace_109885
  have hstable : (prefixWord ++ tailWord_109885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109885).length < 2 ^ (prefixWord ++ tailWord_109885).sum := by decide
  have hdescent : baseEnd_109885 < baseStart_109885 := by decide
  rcases family_descends (prefixWord ++ tailWord_109885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109892 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_109892 : Nat := 118140960795 + 109892 * 2 ^ 59
def prefixEnd_109892 : Nat := 4983230072969 + 3 ^ 40 * 109892 * 2
def baseEnd_109892 : Nat := 50157703185768249550775

theorem tailTrace_109892 : CollatzResearch.WordTrace tailWord_109892 prefixEnd_109892 50157703185768249550775 := by
  unfold tailWord_109892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004045258943763452253965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2672060345258351269671953 2004045258943763452253965)
  ·
    refine ⟨751516972103911294595237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2004045258943763452253965 751516972103911294595237)
    ·
      refine ⟨140909432269483367736607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 751516972103911294595237 140909432269483367736607)
      ·
        refine ⟨211364148404225051604911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140909432269483367736607 211364148404225051604911)
        ·
          refine ⟨317046222606337577407367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211364148404225051604911 317046222606337577407367)
          ·
            refine ⟨475569333909506366111051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317046222606337577407367 475569333909506366111051)
            ·
              refine ⟨713354000864259549166577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475569333909506366111051 713354000864259549166577)
              ·
                refine ⟨535015500648194661874933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713354000864259549166577 535015500648194661874933)
                ·
                  refine ⟨50157703185768249550775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535015500648194661874933 50157703185768249550775)
                  ·
                    rfl

theorem cell20_109892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_109892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109892 prefixEnd_109892 := by exact prefixLift 109892
  have htrace : WordTrace (prefixWord ++ tailWord_109892) baseStart_109892 baseEnd_109892 := by
    simpa [prefixWord, tailWord_109892, baseEnd_109892] using wordTrace_append hprefix tailTrace_109892
  have hstable : (prefixWord ++ tailWord_109892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109892).length < 2 ^ (prefixWord ++ tailWord_109892).sum := by decide
  have hdescent : baseEnd_109892 < baseStart_109892 := by decide
  rcases family_descends (prefixWord ++ tailWord_109892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109992 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_109992 : Nat := 118140960795 + 109992 * 2 ^ 59
def prefixEnd_109992 : Nat := 4983230072969 + 3 ^ 40 * 109992 * 2
def baseEnd_109992 : Nat := 50203345910612346217033

theorem tailTrace_109992 : CollatzResearch.WordTrace tailWord_109992 prefixEnd_109992 50203345910612346217033 := by
  unfold tailWord_109992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005868908762621991574115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2674491878350162655432153 2005868908762621991574115)
  ·
    refine ⟨3008803363143932987361173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2005868908762621991574115 3008803363143932987361173)
    ·
      refine ⟨141037657647371858782555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3008803363143932987361173 141037657647371858782555)
      ·
        refine ⟨211556486471057788173833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141037657647371858782555 211556486471057788173833)
        ·
          refine ⟨158667364853293341130375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211556486471057788173833 158667364853293341130375)
          ·
            refine ⟨238001047279940011695563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158667364853293341130375 238001047279940011695563)
            ·
              refine ⟨357001570919910017543345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238001047279940011695563 357001570919910017543345)
              ·
                refine ⟨267751178189932513157509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357001570919910017543345 267751178189932513157509)
                ·
                  refine ⟨50203345910612346217033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267751178189932513157509 50203345910612346217033)
                  ·
                    rfl

theorem cell20_109992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_109992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_109992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_109992 prefixEnd_109992 := by exact prefixLift 109992
  have htrace : WordTrace (prefixWord ++ tailWord_109992) baseStart_109992 baseEnd_109992 := by
    simpa [prefixWord, tailWord_109992, baseEnd_109992] using wordTrace_append hprefix tailTrace_109992
  have hstable : (prefixWord ++ tailWord_109992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109992).length < 2 ^ (prefixWord ++ tailWord_109992).sum := by decide
  have hdescent : baseEnd_109992 < baseStart_109992 := by decide
  rcases family_descends (prefixWord ++ tailWord_109992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110020 : List Nat := [2, 3, 3, 2, 1, 2, 7]
def baseStart_110020 : Nat := 118140960795 + 110020 * 2 ^ 59
def prefixEnd_110020 : Nat := 4983230072969 + 3 ^ 40 * 110020 * 2
def baseEnd_110020 : Nat := 5579569541507632587065

theorem tailTrace_110020 : CollatzResearch.WordTrace tailWord_110020 prefixEnd_110020 5579569541507632587065 := by
  unfold tailWord_110020
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006379530711902382583757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2675172707615869843445009 2006379530711902382583757)
  ·
    refine ⟨752392324016963393468909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2006379530711902382583757 752392324016963393468909)
    ·
      refine ⟨282147121506361272550841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 752392324016963393468909 282147121506361272550841)
      ·
        refine ⟨211610341129770954413131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282147121506361272550841 211610341129770954413131)
        ·
          refine ⟨317415511694656431619697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211610341129770954413131 317415511694656431619697)
          ·
            refine ⟨238061633770992323714773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317415511694656431619697 238061633770992323714773)
            ·
              refine ⟨5579569541507632587065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238061633770992323714773 5579569541507632587065)
              ·
                rfl

theorem cell20_110020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_110020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110020 prefixEnd_110020 := by exact prefixLift 110020
  have htrace : WordTrace (prefixWord ++ tailWord_110020) baseStart_110020 baseEnd_110020 := by
    simpa [prefixWord, tailWord_110020, baseEnd_110020] using wordTrace_append hprefix tailTrace_110020
  have hstable : (prefixWord ++ tailWord_110020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110020).length < 2 ^ (prefixWord ++ tailWord_110020).sum := by decide
  have hdescent : baseEnd_110020 < baseStart_110020 := by decide
  rcases family_descends (prefixWord ++ tailWord_110020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110027 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_110027 : Nat := 118140960795 + 110027 * 2 ^ 59
def prefixEnd_110027 : Nat := 4983230072969 + 3 ^ 40 * 110027 * 2
def baseEnd_110027 : Nat := 50219320864307780050223

theorem tailTrace_110027 : CollatzResearch.WordTrace tailWord_110027 prefixEnd_110027 50219320864307780050223 := by
  unfold tailWord_110027
  simp only [CollatzResearch.WordTrace]
  refine ⟨4013014372398444960672335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2675342914932296640448223 4013014372398444960672335)
  ·
    refine ⟨6019521558597667441008503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4013014372398444960672335 6019521558597667441008503)
    ·
      refine ⟨9029282337896501161512755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019521558597667441008503 9029282337896501161512755)
      ·
        refine ⟨13543923506844751742269133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9029282337896501161512755 13543923506844751742269133)
        ·
          refine ⟨5078971315066781903350925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13543923506844751742269133 5078971315066781903350925)
          ·
            refine ⟨1904614243150043213756597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5078971315066781903350925 1904614243150043213756597)
            ·
              refine ⟨178557585295316551289681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1904614243150043213756597 178557585295316551289681)
              ·
                refine ⟨133918188971487413467261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178557585295316551289681 133918188971487413467261)
                ·
                  refine ⟨50219320864307780050223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133918188971487413467261 50219320864307780050223)
                  ·
                    rfl

theorem cell20_110027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_110027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110027 prefixEnd_110027 := by exact prefixLift 110027
  have htrace : WordTrace (prefixWord ++ tailWord_110027) baseStart_110027 baseEnd_110027 := by
    simpa [prefixWord, tailWord_110027, baseEnd_110027] using wordTrace_append hprefix tailTrace_110027
  have hstable : (prefixWord ++ tailWord_110027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110027).length < 2 ^ (prefixWord ++ tailWord_110027).sum := by decide
  have hdescent : baseEnd_110027 < baseStart_110027 := by decide
  rcases family_descends (prefixWord ++ tailWord_110027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110058 : List Nat := [3, 1, 3, 1, 4, 1, 1, 6]
def baseStart_110058 : Nat := 118140960795 + 110058 * 2 ^ 59
def prefixEnd_110058 : Nat := 4983230072969 + 3 ^ 40 * 110058 * 2
def baseEnd_110058 : Nat := 16744490036336483338921

theorem tailTrace_110058 : CollatzResearch.WordTrace tailWord_110058 prefixEnd_110058 16744490036336483338921 := by
  unfold tailWord_110058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003536258821534313762707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2676096690190758170033885 1003536258821534313762707)
  ·
    refine ⟨1505304388232301470644061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1003536258821534313762707 1505304388232301470644061)
    ·
      refine ⟨564489145587113051491523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1505304388232301470644061 564489145587113051491523)
      ·
        refine ⟨846733718380669577237285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564489145587113051491523 846733718380669577237285)
        ·
          refine ⟨158762572196375545731991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 846733718380669577237285 158762572196375545731991)
          ·
            refine ⟨238143858294563318597987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158762572196375545731991 238143858294563318597987)
            ·
              refine ⟨357215787441844977896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238143858294563318597987 357215787441844977896981)
              ·
                refine ⟨16744490036336483338921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 357215787441844977896981 16744490036336483338921)
                ·
                  rfl

theorem cell20_110058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_110058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110058 prefixEnd_110058 := by exact prefixLift 110058
  have htrace : WordTrace (prefixWord ++ tailWord_110058) baseStart_110058 baseEnd_110058 := by
    simpa [prefixWord, tailWord_110058, baseEnd_110058] using wordTrace_append hprefix tailTrace_110058
  have hstable : (prefixWord ++ tailWord_110058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110058).length < 2 ^ (prefixWord ++ tailWord_110058).sum := by decide
  have hdescent : baseEnd_110058 < baseStart_110058 := by decide
  rcases family_descends (prefixWord ++ tailWord_110058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110082 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_110082 : Nat := 118140960795 + 110082 * 2 ^ 59
def prefixEnd_110082 : Nat := 4983230072969 + 3 ^ 40 * 110082 * 2
def baseEnd_110082 : Nat := 50244424362972033216665

theorem tailTrace_110082 : CollatzResearch.WordTrace tailWord_110082 prefixEnd_110082 50244424362972033216665 := by
  unfold tailWord_110082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003755096799797338481125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2676680258132792902616333 1003755096799797338481125)
  ·
    refine ⟨188204080649962000965211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1003755096799797338481125 188204080649962000965211)
    ·
      refine ⟨282306120974943001447817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188204080649962000965211 282306120974943001447817)
      ·
        refine ⟨211729590731207251085863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282306120974943001447817 211729590731207251085863)
        ·
          refine ⟨317594386096810876628795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211729590731207251085863 317594386096810876628795)
          ·
            refine ⟨476391579145216314943193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317594386096810876628795 476391579145216314943193)
            ·
              refine ⟨357293684358912236207395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476391579145216314943193 357293684358912236207395)
              ·
                refine ⟨535940526538368354311093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357293684358912236207395 535940526538368354311093)
                ·
                  refine ⟨50244424362972033216665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535940526538368354311093 50244424362972033216665)
                  ·
                    rfl

theorem cell20_110082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_110082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110082 prefixEnd_110082 := by exact prefixLift 110082
  have htrace : WordTrace (prefixWord ++ tailWord_110082) baseStart_110082 baseEnd_110082 := by
    simpa [prefixWord, tailWord_110082, baseEnd_110082] using wordTrace_append hprefix tailTrace_110082
  have hstable : (prefixWord ++ tailWord_110082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110082).length < 2 ^ (prefixWord ++ tailWord_110082).sum := by decide
  have hdescent : baseEnd_110082 < baseStart_110082 := by decide
  rcases family_descends (prefixWord ++ tailWord_110082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110134 : List Nat := [5, 1, 2, 1, 3, 8]
def baseStart_110134 : Nat := 118140960795 + 110134 * 2 ^ 59
def prefixEnd_110134 : Nat := 4983230072969 + 3 ^ 40 * 110134 * 2
def baseEnd_110134 : Nat := 1861783651107072721597

theorem tailTrace_110134 : CollatzResearch.WordTrace tailWord_110134 prefixEnd_110134 1861783651107072721597 := by
  unfold tailWord_110134
  simp only [CollatzResearch.WordTrace]
  refine ⟨251057311438175139676091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2677944655340534823211637 251057311438175139676091)
  ·
    refine ⟨376585967157262709514137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251057311438175139676091 376585967157262709514137)
    ·
      refine ⟨282439475367947032135603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376585967157262709514137 282439475367947032135603)
      ·
        refine ⟨423659213051920548203405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282439475367947032135603 423659213051920548203405)
        ·
          refine ⟨158872204894470205576277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423659213051920548203405 158872204894470205576277)
          ·
            refine ⟨1861783651107072721597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 158872204894470205576277 1861783651107072721597)
            ·
              rfl

theorem cell20_110134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 8].length) (baseStart_110134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110134 prefixEnd_110134 := by exact prefixLift 110134
  have htrace : WordTrace (prefixWord ++ tailWord_110134) baseStart_110134 baseEnd_110134 := by
    simpa [prefixWord, tailWord_110134, baseEnd_110134] using wordTrace_append hprefix tailTrace_110134
  have hstable : (prefixWord ++ tailWord_110134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110134).length < 2 ^ (prefixWord ++ tailWord_110134).sum := by decide
  have hdescent : baseEnd_110134 < baseStart_110134 := by decide
  rcases family_descends (prefixWord ++ tailWord_110134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110140 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 2]
def baseStart_110140 : Nat := 118140960795 + 110140 * 2 ^ 59
def prefixEnd_110140 : Nat := 4983230072969 + 3 ^ 40 * 110140 * 2
def baseEnd_110140 : Nat := 50270897143381609283095

theorem tailTrace_110140 : CollatzResearch.WordTrace tailWord_110140 prefixEnd_110140 50270897143381609283095 := by
  unfold tailWord_110140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008567910494532629767937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2678090547326043506357249 2008567910494532629767937)
  ·
    refine ⟨1506425932870899472325953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2008567910494532629767937 1506425932870899472325953)
    ·
      refine ⟨1129819449653174604244465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1506425932870899472325953 1129819449653174604244465)
      ·
        refine ⟨847364587239880953183349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1129819449653174604244465 847364587239880953183349)
        ·
          refine ⟨79440430053738839360939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 847364587239880953183349 79440430053738839360939)
          ·
            refine ⟨119160645080608259041409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79440430053738839360939 119160645080608259041409)
            ·
              refine ⟨89370483810456194281057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119160645080608259041409 89370483810456194281057)
              ·
                refine ⟨67027862857842145710793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89370483810456194281057 67027862857842145710793)
                ·
                  refine ⟨50270897143381609283095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67027862857842145710793 50270897143381609283095)
                  ·
                    rfl

theorem cell20_110140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_110140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110140 prefixEnd_110140 := by exact prefixLift 110140
  have htrace : WordTrace (prefixWord ++ tailWord_110140) baseStart_110140 baseEnd_110140 := by
    simpa [prefixWord, tailWord_110140, baseEnd_110140] using wordTrace_append hprefix tailTrace_110140
  have hstable : (prefixWord ++ tailWord_110140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110140).length < 2 ^ (prefixWord ++ tailWord_110140).sum := by decide
  have hdescent : baseEnd_110140 < baseStart_110140 := by decide
  rcases family_descends (prefixWord ++ tailWord_110140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110151 : List Nat := [1, 1, 4, 1, 6, 1, 1, 5]
def baseStart_110151 : Nat := 118140960795 + 110151 * 2 ^ 59
def prefixEnd_110151 : Nat := 4983230072969 + 3 ^ 40 * 110151 * 2
def baseEnd_110151 : Nat := 16758639281038153305461

theorem tailTrace_110151 : CollatzResearch.WordTrace tailWord_110151 prefixEnd_110151 16758639281038153305461 := by
  unfold tailWord_110151
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017537023949214138186307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2678358015966142758790871 4017537023949214138186307)
  ·
    refine ⟨6026305535923821207279461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4017537023949214138186307 6026305535923821207279461)
    ·
      refine ⟨1129932287985716476364899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6026305535923821207279461 1129932287985716476364899)
      ·
        refine ⟨1694898431978574714547349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129932287985716476364899 1694898431978574714547349)
        ·
          refine ⟨79448363998995689744407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1694898431978574714547349 79448363998995689744407)
          ·
            refine ⟨119172545998493534616611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79448363998995689744407 119172545998493534616611)
            ·
              refine ⟨178758818997740301924917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119172545998493534616611 178758818997740301924917)
              ·
                refine ⟨16758639281038153305461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178758818997740301924917 16758639281038153305461)
                ·
                  rfl

theorem cell20_110151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].length) (baseStart_110151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110151 prefixEnd_110151 := by exact prefixLift 110151
  have htrace : WordTrace (prefixWord ++ tailWord_110151) baseStart_110151 baseEnd_110151 := by
    simpa [prefixWord, tailWord_110151, baseEnd_110151] using wordTrace_append hprefix tailTrace_110151
  have hstable : (prefixWord ++ tailWord_110151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110151).length < 2 ^ (prefixWord ++ tailWord_110151).sum := by decide
  have hdescent : baseEnd_110151 < baseStart_110151 := by decide
  rcases family_descends (prefixWord ++ tailWord_110151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110231 : List Nat := [1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_110231 : Nat := 118140960795 + 110231 * 2 ^ 59
def prefixEnd_110231 : Nat := 4983230072969 + 3 ^ 40 * 110231 * 2
def baseEnd_110231 : Nat := 16770810674329912416463

theorem tailTrace_110231 : CollatzResearch.WordTrace tailWord_110231 prefixEnd_110231 16770810674329912416463 := by
  unfold tailWord_110231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020454863659387801098547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2680303242439591867399031 4020454863659387801098547)
  ·
    refine ⟨6030682295489081701647821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4020454863659387801098547 6030682295489081701647821)
    ·
      refine ⟨2261505860808405638117933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6030682295489081701647821 2261505860808405638117933)
      ·
        refine ⟨848064697803152114294225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2261505860808405638117933 848064697803152114294225)
        ·
          refine ⟨636048523352364085720669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848064697803152114294225 636048523352364085720669)
          ·
            refine ⟨238518196257136532145251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636048523352364085720669 238518196257136532145251)
            ·
              refine ⟨357777294385704798217877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238518196257136532145251 357777294385704798217877)
              ·
                refine ⟨16770810674329912416463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 357777294385704798217877 16770810674329912416463)
                ·
                  rfl

theorem cell20_110231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_110231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110231 prefixEnd_110231 := by exact prefixLift 110231
  have htrace : WordTrace (prefixWord ++ tailWord_110231) baseStart_110231 baseEnd_110231 := by
    simpa [prefixWord, tailWord_110231, baseEnd_110231] using wordTrace_append hprefix tailTrace_110231
  have hstable : (prefixWord ++ tailWord_110231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110231).length < 2 ^ (prefixWord ++ tailWord_110231).sum := by decide
  have hdescent : baseEnd_110231 < baseStart_110231 := by decide
  rcases family_descends (prefixWord ++ tailWord_110231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110245 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_110245 : Nat := 118140960795 + 110245 * 2 ^ 59
def prefixEnd_110245 : Nat := 4983230072969 + 3 ^ 40 * 110245 * 2
def baseEnd_110245 : Nat := 50318822004467910782665

theorem tailTrace_110245 : CollatzResearch.WordTrace tailWord_110245 prefixEnd_110245 50318822004467910782665 := by
  unfold tailWord_110245
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020965485608668192108189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2680643657072445461405459 4020965485608668192108189)
  ·
    refine ⟨1507862057103250572040571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4020965485608668192108189 1507862057103250572040571)
    ·
      refine ⟨2261793085654875858060857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507862057103250572040571 2261793085654875858060857)
      ·
        refine ⟨1696344814241156893545643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2261793085654875858060857 1696344814241156893545643)
        ·
          refine ⟨2544517221361735340318465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696344814241156893545643 2544517221361735340318465)
          ·
            refine ⟨1908387916021301505238849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544517221361735340318465 1908387916021301505238849)
            ·
              refine ⟨1431290937015976128929137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908387916021301505238849 1431290937015976128929137)
              ·
                refine ⟨1073468202761982096696853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431290937015976128929137 1073468202761982096696853)
                ·
                  refine ⟨50318822004467910782665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1073468202761982096696853 50318822004467910782665)
                  ·
                    rfl

theorem cell20_110245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_110245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110245 prefixEnd_110245 := by exact prefixLift 110245
  have htrace : WordTrace (prefixWord ++ tailWord_110245) baseStart_110245 baseEnd_110245 := by
    simpa [prefixWord, tailWord_110245, baseEnd_110245] using wordTrace_append hprefix tailTrace_110245
  have hstable : (prefixWord ++ tailWord_110245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110245).length < 2 ^ (prefixWord ++ tailWord_110245).sum := by decide
  have hdescent : baseEnd_110245 < baseStart_110245 := by decide
  rcases family_descends (prefixWord ++ tailWord_110245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110254 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_110254 : Nat := 118140960795 + 110254 * 2 ^ 59
def prefixEnd_110254 : Nat := 4983230072969 + 3 ^ 40 * 110254 * 2
def baseEnd_110254 : Nat := 50322929849703879482629

theorem tailTrace_110254 : CollatzResearch.WordTrace tailWord_110254 prefixEnd_110254 50322929849703879482629 := by
  unfold tailWord_110254
  simp only [CollatzResearch.WordTrace]
  refine ⟨502661717822007841148227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2680862495050708486123877 502661717822007841148227)
  ·
    refine ⟨753992576733011761722341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 502661717822007841148227 753992576733011761722341)
    ·
      refine ⟨141373608137439705322939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 753992576733011761722341 141373608137439705322939)
      ·
        refine ⟨212060412206159557984409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141373608137439705322939 212060412206159557984409)
        ·
          refine ⟨159045309154619668488307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212060412206159557984409 159045309154619668488307)
          ·
            refine ⟨238567963731929502732461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159045309154619668488307 238567963731929502732461)
            ·
              refine ⟨89462986399473563524673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238567963731929502732461 89462986399473563524673)
              ·
                refine ⟨67097239799605172643505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89462986399473563524673 67097239799605172643505)
                ·
                  refine ⟨50322929849703879482629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67097239799605172643505 50322929849703879482629)
                  ·
                    rfl

theorem cell20_110254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_110254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110254 prefixEnd_110254 := by exact prefixLift 110254
  have htrace : WordTrace (prefixWord ++ tailWord_110254) baseStart_110254 baseEnd_110254 := by
    simpa [prefixWord, tailWord_110254, baseEnd_110254] using wordTrace_append hprefix tailTrace_110254
  have hstable : (prefixWord ++ tailWord_110254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110254).length < 2 ^ (prefixWord ++ tailWord_110254).sum := by decide
  have hdescent : baseEnd_110254 < baseStart_110254 := by decide
  rcases family_descends (prefixWord ++ tailWord_110254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110269 : List Nat := [1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_110269 : Nat := 118140960795 + 110269 * 2 ^ 59
def prefixEnd_110269 : Nat := 4983230072969 + 3 ^ 40 * 110269 * 2
def baseEnd_110269 : Nat := 16776592086143497994189

theorem tailTrace_110269 : CollatzResearch.WordTrace tailWord_110269 prefixEnd_110269 16776592086143497994189 := by
  unfold tailWord_110269
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021840837521720290981861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2681227225014480193987907 4021840837521720290981861)
  ·
    refine ⟨754095157035322554559099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4021840837521720290981861 754095157035322554559099)
    ·
      refine ⟨1131142735552983831838649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754095157035322554559099 1131142735552983831838649)
      ·
        refine ⟨848357051664737873878987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131142735552983831838649 848357051664737873878987)
        ·
          refine ⟨1272535577497106810818481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848357051664737873878987 1272535577497106810818481)
          ·
            refine ⟨954401683122830108113861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272535577497106810818481 954401683122830108113861)
            ·
              refine ⟨178950315585530645271349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 954401683122830108113861 178950315585530645271349)
              ·
                refine ⟨16776592086143497994189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178950315585530645271349 16776592086143497994189)
                ·
                  rfl

theorem cell20_110269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_110269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110269 prefixEnd_110269 := by exact prefixLift 110269
  have htrace : WordTrace (prefixWord ++ tailWord_110269) baseStart_110269 baseEnd_110269 := by
    simpa [prefixWord, tailWord_110269, baseEnd_110269] using wordTrace_append hprefix tailTrace_110269
  have hstable : (prefixWord ++ tailWord_110269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110269).length < 2 ^ (prefixWord ++ tailWord_110269).sum := by decide
  have hdescent : baseEnd_110269 < baseStart_110269 := by decide
  rcases family_descends (prefixWord ++ tailWord_110269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110283 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_110283 : Nat := 118140960795 + 110283 * 2 ^ 59
def prefixEnd_110283 : Nat := 4983230072969 + 3 ^ 40 * 110283 * 2
def baseEnd_110283 : Nat := 50336166239908667515843

theorem tailTrace_110283 : CollatzResearch.WordTrace tailWord_110283 prefixEnd_110283 50336166239908667515843 := by
  unfold tailWord_110283
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022351459471000681991503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2681567639647333787994335 4022351459471000681991503)
  ·
    refine ⟨6033527189206501022987255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4022351459471000681991503 6033527189206501022987255)
    ·
      refine ⟨9050290783809751534480883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033527189206501022987255 9050290783809751534480883)
      ·
        refine ⟨13575436175714627301721325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9050290783809751534480883 13575436175714627301721325)
        ·
          refine ⟨5090788565892985238145497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13575436175714627301721325 5090788565892985238145497)
          ·
            refine ⟨3818091424419738928609123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090788565892985238145497 3818091424419738928609123)
            ·
              refine ⟨5727137136629608392913685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818091424419738928609123 5727137136629608392913685)
              ·
                refine ⟨268459553279512893417829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5727137136629608392913685 268459553279512893417829)
                ·
                  refine ⟨50336166239908667515843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268459553279512893417829 50336166239908667515843)
                  ·
                    rfl

theorem cell20_110283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_110283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110283 prefixEnd_110283 := by exact prefixLift 110283
  have htrace : WordTrace (prefixWord ++ tailWord_110283) baseStart_110283 baseEnd_110283 := by
    simpa [prefixWord, tailWord_110283, baseEnd_110283] using wordTrace_append hprefix tailTrace_110283
  have hstable : (prefixWord ++ tailWord_110283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110283).length < 2 ^ (prefixWord ++ tailWord_110283).sum := by decide
  have hdescent : baseEnd_110283 < baseStart_110283 := by decide
  rcases family_descends (prefixWord ++ tailWord_110283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110307 : List Nat := [1, 1, 1, 7, 2, 8]
def baseStart_110307 : Nat := 118140960795 + 110307 * 2 ^ 59
def prefixEnd_110307 : Nat := 4983230072969 + 3 ^ 40 * 110307 * 2
def baseEnd_110307 : Nat := 1864708166439675952435

theorem tailTrace_110307 : CollatzResearch.WordTrace tailWord_110307 prefixEnd_110307 1864708166439675952435 := by
  unfold tailWord_110307
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023226811384052780865175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2682151207589368520576783 4023226811384052780865175)
  ·
    refine ⟨6034840217076079171297763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023226811384052780865175 6034840217076079171297763)
    ·
      refine ⟨9052260325614118756946645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034840217076079171297763 9052260325614118756946645)
      ·
        refine ⟨212162351381580908365937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9052260325614118756946645 212162351381580908365937)
        ·
          refine ⟨159121763536185681274453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212162351381580908365937 159121763536185681274453)
          ·
            refine ⟨1864708166439675952435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 159121763536185681274453 1864708166439675952435)
            ·
              rfl

theorem cell20_110307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 8].length) (baseStart_110307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110307 prefixEnd_110307 := by exact prefixLift 110307
  have htrace : WordTrace (prefixWord ++ tailWord_110307) baseStart_110307 baseEnd_110307 := by
    simpa [prefixWord, tailWord_110307, baseEnd_110307] using wordTrace_append hprefix tailTrace_110307
  have hstable : (prefixWord ++ tailWord_110307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110307).length < 2 ^ (prefixWord ++ tailWord_110307).sum := by decide
  have hdescent : baseEnd_110307 < baseStart_110307 := by decide
  rcases family_descends (prefixWord ++ tailWord_110307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110314 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_110314 : Nat := 118140960795 + 110314 * 2 ^ 59
def prefixEnd_110314 : Nat := 4983230072969 + 3 ^ 40 * 110314 * 2
def baseEnd_110314 : Nat := 50350315484610337482383

theorem tailTrace_110314 : CollatzResearch.WordTrace tailWord_110314 prefixEnd_110314 50350315484610337482383 := by
  unfold tailWord_110314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005870530589673244092499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2682321414905795317579997 1005870530589673244092499)
  ·
    refine ⟨1508805795884509866138749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1005870530589673244092499 1508805795884509866138749)
    ·
      refine ⟨565802173456691199802031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1508805795884509866138749 565802173456691199802031)
      ·
        refine ⟨848703260185036799703047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565802173456691199802031 848703260185036799703047)
        ·
          refine ⟨1273054890277555199554571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848703260185036799703047 1273054890277555199554571)
          ·
            refine ⟨1909582335416332799331857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273054890277555199554571 1909582335416332799331857)
            ·
              refine ⟨1432186751562249599498893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909582335416332799331857 1432186751562249599498893)
              ·
                refine ⟨537070031835843599812085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432186751562249599498893 537070031835843599812085)
                ·
                  refine ⟨50350315484610337482383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 537070031835843599812085 50350315484610337482383)
                  ·
                    rfl

theorem cell20_110314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_110314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110314 prefixEnd_110314 := by exact prefixLift 110314
  have htrace : WordTrace (prefixWord ++ tailWord_110314) baseStart_110314 baseEnd_110314 := by
    simpa [prefixWord, tailWord_110314, baseEnd_110314] using wordTrace_append hprefix tailTrace_110314
  have hstable : (prefixWord ++ tailWord_110314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110314).length < 2 ^ (prefixWord ++ tailWord_110314).sum := by decide
  have hdescent : baseEnd_110314 < baseStart_110314 := by decide
  rcases family_descends (prefixWord ++ tailWord_110314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110328 : List Nat := [2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_110328 : Nat := 118140960795 + 110328 * 2 ^ 59
def prefixEnd_110328 : Nat := 4983230072969 + 3 ^ 40 * 110328 * 2
def baseEnd_110328 : Nat := 16785568488696170338553

theorem tailTrace_110328 : CollatzResearch.WordTrace tailWord_110328 prefixEnd_110328 16785568488696170338553 := by
  unfold tailWord_110328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011996372153986683689819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2682661829538648911586425 2011996372153986683689819)
  ·
    refine ⟨3017994558230980025534729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2011996372153986683689819 3017994558230980025534729)
    ·
      refine ⟨2263495918673235019151047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3017994558230980025534729 2263495918673235019151047)
      ·
        refine ⟨3395243878009852528726571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263495918673235019151047 3395243878009852528726571)
        ·
          refine ⟨5092865817014778793089857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395243878009852528726571 5092865817014778793089857)
          ·
            refine ⟨3819649362761084094817393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092865817014778793089857 3819649362761084094817393)
            ·
              refine ⟨2864737022070813071113045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819649362761084094817393 2864737022070813071113045)
              ·
                refine ⟨16785568488696170338553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2864737022070813071113045 16785568488696170338553)
                ·
                  rfl

theorem cell20_110328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_110328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110328 prefixEnd_110328 := by exact prefixLift 110328
  have htrace : WordTrace (prefixWord ++ tailWord_110328) baseStart_110328 baseEnd_110328 := by
    simpa [prefixWord, tailWord_110328, baseEnd_110328] using wordTrace_append hprefix tailTrace_110328
  have hstable : (prefixWord ++ tailWord_110328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110328).length < 2 ^ (prefixWord ++ tailWord_110328).sum := by decide
  have hdescent : baseEnd_110328 < baseStart_110328 := by decide
  rcases family_descends (prefixWord ++ tailWord_110328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110369 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_110369 : Nat := 118140960795 + 110369 * 2 ^ 59
def prefixEnd_110369 : Nat := 4983230072969 + 3 ^ 40 * 110369 * 2
def baseEnd_110369 : Nat := 50375418983274590648825

theorem tailTrace_110369 : CollatzResearch.WordTrace tailWord_110369 prefixEnd_110369 50375418983274590648825 := by
  unfold tailWord_110369
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025488137159437369622161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2683658758106291579748107 4025488137159437369622161)
  ·
    refine ⟨3019116102869578027216621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4025488137159437369622161 3019116102869578027216621)
    ·
      refine ⟨1132168538576091760206233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3019116102869578027216621 1132168538576091760206233)
      ·
        refine ⟨849126403932068820154675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1132168538576091760206233 849126403932068820154675)
        ·
          refine ⟨1273689605898103230232013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849126403932068820154675 1273689605898103230232013)
          ·
            refine ⟨477633602211788711337005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1273689605898103230232013 477633602211788711337005)
            ·
              refine ⟨179112600829420766751377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 477633602211788711337005 179112600829420766751377)
              ·
                refine ⟨134334450622065575063533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179112600829420766751377 134334450622065575063533)
                ·
                  refine ⟨50375418983274590648825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134334450622065575063533 50375418983274590648825)
                  ·
                    rfl

theorem cell20_110369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_110369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110369 prefixEnd_110369 := by exact prefixLift 110369
  have htrace : WordTrace (prefixWord ++ tailWord_110369) baseStart_110369 baseEnd_110369 := by
    simpa [prefixWord, tailWord_110369, baseEnd_110369] using wordTrace_append hprefix tailTrace_110369
  have hstable : (prefixWord ++ tailWord_110369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110369).length < 2 ^ (prefixWord ++ tailWord_110369).sum := by decide
  have hdescent : baseEnd_110369 < baseStart_110369 := by decide
  rcases family_descends (prefixWord ++ tailWord_110369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110376 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_110376 : Nat := 118140960795 + 110376 * 2 ^ 59
def prefixEnd_110376 : Nat := 4983230072969 + 3 ^ 40 * 110376 * 2
def baseEnd_110376 : Nat := 50378613974013677415463

theorem tailTrace_110376 : CollatzResearch.WordTrace tailWord_110376 prefixEnd_110376 50378613974013677415463 := by
  unfold tailWord_110376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012871724067038782563491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2683828965422718376751321 2012871724067038782563491)
  ·
    refine ⟨3019307586100558173845237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2012871724067038782563491 3019307586100558173845237)
    ·
      refine ⟨283060086196927328797991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3019307586100558173845237 283060086196927328797991)
      ·
        refine ⟨424590129295390993196987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283060086196927328797991 424590129295390993196987)
        ·
          refine ⟨636885193943086489795481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424590129295390993196987 636885193943086489795481)
          ·
            refine ⟨477663895457314867346611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636885193943086489795481 477663895457314867346611)
            ·
              refine ⟨716495843185972301019917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477663895457314867346611 716495843185972301019917)
              ·
                refine ⟨268685941194739612882469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716495843185972301019917 268685941194739612882469)
                ·
                  refine ⟨50378613974013677415463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268685941194739612882469 50378613974013677415463)
                  ·
                    rfl

theorem cell20_110376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_110376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110376 prefixEnd_110376 := by exact prefixLift 110376
  have htrace : WordTrace (prefixWord ++ tailWord_110376) baseStart_110376 baseEnd_110376 := by
    simpa [prefixWord, tailWord_110376, baseEnd_110376] using wordTrace_append hprefix tailTrace_110376
  have hstable : (prefixWord ++ tailWord_110376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110376).length < 2 ^ (prefixWord ++ tailWord_110376).sum := by decide
  have hdescent : baseEnd_110376 < baseStart_110376 := by decide
  rcases family_descends (prefixWord ++ tailWord_110376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110386 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_110386 : Nat := 118140960795 + 110386 * 2 ^ 59
def prefixEnd_110386 : Nat := 4983230072969 + 3 ^ 40 * 110386 * 2
def baseEnd_110386 : Nat := 50383178246498087082089

theorem tailTrace_110386 : CollatzResearch.WordTrace tailWord_110386 prefixEnd_110386 50383178246498087082089 := by
  unfold tailWord_110386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006527044524462318247753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2684072118731899515327341 1006527044524462318247753)
  ·
    refine ⟨754895283393346738685815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1006527044524462318247753 754895283393346738685815)
    ·
      refine ⟨1132342925090020108028723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754895283393346738685815 1132342925090020108028723)
      ·
        refine ⟨1698514387635030162043085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132342925090020108028723 1698514387635030162043085)
        ·
          refine ⟨636942895363136310766157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1698514387635030162043085 636942895363136310766157)
          ·
            refine ⟨238853585761176116537309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636942895363136310766157 238853585761176116537309)
            ·
              refine ⟨89570094660441043701491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238853585761176116537309 89570094660441043701491)
              ·
                refine ⟨134355141990661565552237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89570094660441043701491 134355141990661565552237)
                ·
                  refine ⟨50383178246498087082089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134355141990661565552237 50383178246498087082089)
                  ·
                    rfl

theorem cell20_110386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_110386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110386 prefixEnd_110386 := by exact prefixLift 110386
  have htrace : WordTrace (prefixWord ++ tailWord_110386) baseStart_110386 baseEnd_110386 := by
    simpa [prefixWord, tailWord_110386, baseEnd_110386] using wordTrace_append hprefix tailTrace_110386
  have hstable : (prefixWord ++ tailWord_110386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110386).length < 2 ^ (prefixWord ++ tailWord_110386).sum := by decide
  have hdescent : baseEnd_110386 < baseStart_110386 := by decide
  rcases family_descends (prefixWord ++ tailWord_110386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110406 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_110406 : Nat := 118140960795 + 110406 * 2 ^ 59
def prefixEnd_110406 : Nat := 4983230072969 + 3 ^ 40 * 110406 * 2
def baseEnd_110406 : Nat := 50392306791466906415341

theorem tailTrace_110406 : CollatzResearch.WordTrace tailWord_110406 prefixEnd_110406 50392306791466906415341 := by
  unfold tailWord_110406
  simp only [CollatzResearch.WordTrace]
  refine ⟨125838676188293521522471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2684558425350261792479381 125838676188293521522471)
  ·
    refine ⟨188758014282440282283707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125838676188293521522471 188758014282440282283707)
    ·
      refine ⟨283137021423660423425561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188758014282440282283707 283137021423660423425561)
      ·
        refine ⟨212352766067745317569171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283137021423660423425561 212352766067745317569171)
        ·
          refine ⟨318529149101617976353757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212352766067745317569171 318529149101617976353757)
          ·
            refine ⟨119448430913106741132659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318529149101617976353757 119448430913106741132659)
            ·
              refine ⟨179172646369660111698989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119448430913106741132659 179172646369660111698989)
              ·
                refine ⟨67189742388622541887121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179172646369660111698989 67189742388622541887121)
                ·
                  refine ⟨50392306791466906415341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67189742388622541887121 50392306791466906415341)
                  ·
                    rfl

theorem cell20_110406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_110406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110406 prefixEnd_110406 := by exact prefixLift 110406
  have htrace : WordTrace (prefixWord ++ tailWord_110406) baseStart_110406 baseEnd_110406 := by
    simpa [prefixWord, tailWord_110406, baseEnd_110406] using wordTrace_append hprefix tailTrace_110406
  have hstable : (prefixWord ++ tailWord_110406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110406).length < 2 ^ (prefixWord ++ tailWord_110406).sum := by decide
  have hdescent : baseEnd_110406 < baseStart_110406 := by decide
  rcases family_descends (prefixWord ++ tailWord_110406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110421 : List Nat := [1, 3, 2, 2, 2, 4, 6]
def baseStart_110421 : Nat := 118140960795 + 110421 * 2 ^ 59
def prefixEnd_110421 : Nat := 4983230072969 + 3 ^ 40 * 110421 * 2
def baseEnd_110421 : Nat := 5599905911132613435031

theorem tailTrace_110421 : CollatzResearch.WordTrace tailWord_110421 prefixEnd_110421 5599905911132613435031 := by
  unfold tailWord_110421
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027384732971050250515117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2684923155314033500343411 4027384732971050250515117)
  ·
    refine ⟨1510269274864143843943169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4027384732971050250515117 1510269274864143843943169)
    ·
      refine ⟨1132701956148107882957377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1510269274864143843943169 1132701956148107882957377)
      ·
        refine ⟨849526467111080912218033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1132701956148107882957377 849526467111080912218033)
        ·
          refine ⟨637144850333310684163525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849526467111080912218033 637144850333310684163525)
          ·
            refine ⟨119464659437495753280661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 637144850333310684163525 119464659437495753280661)
            ·
              refine ⟨5599905911132613435031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119464659437495753280661 5599905911132613435031)
              ·
                rfl

theorem cell20_110421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_110421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110421 prefixEnd_110421 := by exact prefixLift 110421
  have htrace : WordTrace (prefixWord ++ tailWord_110421) baseStart_110421 baseEnd_110421 := by
    simpa [prefixWord, tailWord_110421, baseEnd_110421] using wordTrace_append hprefix tailTrace_110421
  have hstable : (prefixWord ++ tailWord_110421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110421).length < 2 ^ (prefixWord ++ tailWord_110421).sum := by decide
  have hdescent : baseEnd_110421 < baseStart_110421 := by decide
  rcases family_descends (prefixWord ++ tailWord_110421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110511 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_110511 : Nat := 118140960795 + 110511 * 2 ^ 59
def prefixEnd_110511 : Nat := 4983230072969 + 3 ^ 40 * 110511 * 2
def baseEnd_110511 : Nat := 50440231652553207914911

theorem tailTrace_110511 : CollatzResearch.WordTrace tailWord_110511 prefixEnd_110511 50440231652553207914911 := by
  unfold tailWord_110511
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030667302644995621291387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2687111535096663747527591 4030667302644995621291387)
  ·
    refine ⟨6046000953967493431937081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030667302644995621291387 6046000953967493431937081)
    ·
      refine ⟨4534500715475620073952811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6046000953967493431937081 4534500715475620073952811)
      ·
        refine ⟨6801751073213430110929217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534500715475620073952811 6801751073213430110929217)
        ·
          refine ⟨5101313304910072583196913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6801751073213430110929217 5101313304910072583196913)
          ·
            refine ⟨3825984978682554437397685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101313304910072583196913 3825984978682554437397685)
            ·
              refine ⟨358686091751489478506033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3825984978682554437397685 358686091751489478506033)
              ·
                refine ⟨269014568813617108879525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358686091751489478506033 269014568813617108879525)
                ·
                  refine ⟨50440231652553207914911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269014568813617108879525 50440231652553207914911)
                  ·
                    rfl

theorem cell20_110511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_110511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110511 prefixEnd_110511 := by exact prefixLift 110511
  have htrace : WordTrace (prefixWord ++ tailWord_110511) baseStart_110511 baseEnd_110511 := by
    simpa [prefixWord, tailWord_110511, baseEnd_110511] using wordTrace_append hprefix tailTrace_110511
  have hstable : (prefixWord ++ tailWord_110511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110511).length < 2 ^ (prefixWord ++ tailWord_110511).sum := by decide
  have hdescent : baseEnd_110511 < baseStart_110511 := by decide
  rcases family_descends (prefixWord ++ tailWord_110511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110542 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_110542 : Nat := 118140960795 + 110542 * 2 ^ 59
def prefixEnd_110542 : Nat := 4983230072969 + 3 ^ 40 * 110542 * 2
def baseEnd_110542 : Nat := 50454380897254877881451

theorem tailTrace_110542 : CollatzResearch.WordTrace tailWord_110542 prefixEnd_110542 50454380897254877881451 := by
  unfold tailWord_110542
  simp only [CollatzResearch.WordTrace]
  refine ⟨503974745691585989458735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2687865310355125277113253 503974745691585989458735)
  ·
    refine ⟨755962118537378984188103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503974745691585989458735 755962118537378984188103)
    ·
      refine ⟨1133943177806068476282155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755962118537378984188103 1133943177806068476282155)
      ·
        refine ⟨1700914766709102714423233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133943177806068476282155 1700914766709102714423233)
        ·
          refine ⟨1275686075031827035817425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700914766709102714423233 1275686075031827035817425)
          ·
            refine ⟨956764556273870276863069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275686075031827035817425 956764556273870276863069)
            ·
              refine ⟨358786708602701353823651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 956764556273870276863069 358786708602701353823651)
              ·
                refine ⟨538180062904052030735477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358786708602701353823651 538180062904052030735477)
                ·
                  refine ⟨50454380897254877881451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 538180062904052030735477 50454380897254877881451)
                  ·
                    rfl

theorem cell20_110542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_110542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110542 prefixEnd_110542 := by exact prefixLift 110542
  have htrace : WordTrace (prefixWord ++ tailWord_110542) baseStart_110542 baseEnd_110542 := by
    simpa [prefixWord, tailWord_110542, baseEnd_110542] using wordTrace_append hprefix tailTrace_110542
  have hstable : (prefixWord ++ tailWord_110542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110542).length < 2 ^ (prefixWord ++ tailWord_110542).sum := by decide
  have hdescent : baseEnd_110542 < baseStart_110542 := by decide
  rcases family_descends (prefixWord ++ tailWord_110542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110590 : List Nat := [4, 2, 2, 2, 1, 3, 6]
def baseStart_110590 : Nat := 118140960795 + 110590 * 2 ^ 59
def prefixEnd_110590 : Nat := 4983230072969 + 3 ^ 40 * 110590 * 2
def baseEnd_110590 : Nat := 5608476600575560475695

theorem tailTrace_110590 : CollatzResearch.WordTrace tailWord_110590 prefixEnd_110590 5608476600575560475695 := by
  unfold tailWord_110590
  simp only [CollatzResearch.WordTrace]
  refine ⟨504193583669849014177153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2689032446239194742278149 504193583669849014177153)
  ·
    refine ⟨378145187752386760632865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 504193583669849014177153 378145187752386760632865)
    ·
      refine ⟨283608890814290070474649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378145187752386760632865 283608890814290070474649)
      ·
        refine ⟨212706668110717552855987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283608890814290070474649 212706668110717552855987)
        ·
          refine ⟨319060002166076329283981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212706668110717552855987 319060002166076329283981)
          ·
            refine ⟨119647500812278623481493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319060002166076329283981 119647500812278623481493)
            ·
              refine ⟨5608476600575560475695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119647500812278623481493 5608476600575560475695)
              ·
                rfl

theorem cell20_110590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 6].length) (baseStart_110590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110590 prefixEnd_110590 := by exact prefixLift 110590
  have htrace : WordTrace (prefixWord ++ tailWord_110590) baseStart_110590 baseEnd_110590 := by
    simpa [prefixWord, tailWord_110590, baseEnd_110590] using wordTrace_append hprefix tailTrace_110590
  have hstable : (prefixWord ++ tailWord_110590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110590).length < 2 ^ (prefixWord ++ tailWord_110590).sum := by decide
  have hdescent : baseEnd_110590 < baseStart_110590 := by decide
  rcases family_descends (prefixWord ++ tailWord_110590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110639 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_110639 : Nat := 118140960795 + 110639 * 2 ^ 59
def prefixEnd_110639 : Nat := 4983230072969 + 3 ^ 40 * 110639 * 2
def baseEnd_110639 : Nat := 50498654340353651647721

theorem tailTrace_110639 : CollatzResearch.WordTrace tailWord_110639 prefixEnd_110639 50498654340353651647721 := by
  unfold tailWord_110639
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035335846181273481950971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2690223897454182321300647 4035335846181273481950971)
  ·
    refine ⟨6053003769271910222926457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4035335846181273481950971 6053003769271910222926457)
    ·
      refine ⟨4539752826953932667194843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6053003769271910222926457 4539752826953932667194843)
      ·
        refine ⟨6809629240430899000792265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539752826953932667194843 6809629240430899000792265)
        ·
          refine ⟨5107221930323174250594199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6809629240430899000792265 5107221930323174250594199)
          ·
            refine ⟨7660832895484761375891299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107221930323174250594199 7660832895484761375891299)
            ·
              refine ⟨11491249343227142063836949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660832895484761375891299 11491249343227142063836949)
              ·
                refine ⟨538652312963772284242357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11491249343227142063836949 538652312963772284242357)
                ·
                  refine ⟨50498654340353651647721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 538652312963772284242357 50498654340353651647721)
                  ·
                    rfl

theorem cell20_110639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_110639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110639 prefixEnd_110639 := by exact prefixLift 110639
  have htrace : WordTrace (prefixWord ++ tailWord_110639) baseStart_110639 baseEnd_110639 := by
    simpa [prefixWord, tailWord_110639, baseEnd_110639] using wordTrace_append hprefix tailTrace_110639
  have hstable : (prefixWord ++ tailWord_110639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110639).length < 2 ^ (prefixWord ++ tailWord_110639).sum := by decide
  have hdescent : baseEnd_110639 < baseStart_110639 := by decide
  rcases family_descends (prefixWord ++ tailWord_110639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110649 : List Nat := [1, 2, 1, 5, 4, 7]
def baseStart_110649 : Nat := 118140960795 + 110649 * 2 ^ 59
def prefixEnd_110649 : Nat := 4983230072969 + 3 ^ 40 * 110649 * 2
def baseEnd_110649 : Nat := 1870489578253261530161

theorem tailTrace_110649 : CollatzResearch.WordTrace tailWord_110649 prefixEnd_110649 1870489578253261530161 := by
  unfold tailWord_110649
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035700576145045189815001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2690467050763363459876667 4035700576145045189815001)
  ·
    refine ⟨3026775432108783892361251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4035700576145045189815001 3026775432108783892361251)
    ·
      refine ⟨4540163148163175838541877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026775432108783892361251 4540163148163175838541877)
      ·
        refine ⟨425640295140297734863301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4540163148163175838541877 425640295140297734863301)
        ·
          refine ⟨79807555338805825286869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425640295140297734863301 79807555338805825286869)
          ·
            refine ⟨1870489578253261530161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 79807555338805825286869 1870489578253261530161)
            ·
              rfl

theorem cell20_110649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 7].length) (baseStart_110649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110649 prefixEnd_110649 := by exact prefixLift 110649
  have htrace : WordTrace (prefixWord ++ tailWord_110649) baseStart_110649 baseEnd_110649 := by
    simpa [prefixWord, tailWord_110649, baseEnd_110649] using wordTrace_append hprefix tailTrace_110649
  have hstable : (prefixWord ++ tailWord_110649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110649).length < 2 ^ (prefixWord ++ tailWord_110649).sum := by decide
  have hdescent : baseEnd_110649 < baseStart_110649 := by decide
  rcases family_descends (prefixWord ++ tailWord_110649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110656 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_110656 : Nat := 118140960795 + 110656 * 2 ^ 59
def prefixEnd_110656 : Nat := 4983230072969 + 3 ^ 40 * 110656 * 2
def baseEnd_110656 : Nat := 50506413603577148080985

theorem tailTrace_110656 : CollatzResearch.WordTrace tailWord_110656 prefixEnd_110656 50506413603577148080985 := by
  unfold tailWord_110656
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017977943559842692659911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2690637258079790256879881 2017977943559842692659911)
  ·
    refine ⟨3026966915339764038989867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2017977943559842692659911 3026966915339764038989867)
    ·
      refine ⟨4540450373009646058484801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026966915339764038989867 4540450373009646058484801)
      ·
        refine ⟨3405337779757234543863601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4540450373009646058484801 3405337779757234543863601)
        ·
          refine ⟨2554003334817925907897701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3405337779757234543863601 2554003334817925907897701)
          ·
            refine ⟨478875625278361107730819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2554003334817925907897701 478875625278361107730819)
            ·
              refine ⟨718313437917541661596229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478875625278361107730819 718313437917541661596229)
              ·
                refine ⟨134683769609539061549293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718313437917541661596229 134683769609539061549293)
                ·
                  refine ⟨50506413603577148080985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134683769609539061549293 50506413603577148080985)
                  ·
                    rfl

theorem cell20_110656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_110656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110656 prefixEnd_110656 := by exact prefixLift 110656
  have htrace : WordTrace (prefixWord ++ tailWord_110656) baseStart_110656 baseEnd_110656 := by
    simpa [prefixWord, tailWord_110656, baseEnd_110656] using wordTrace_append hprefix tailTrace_110656
  have hstable : (prefixWord ++ tailWord_110656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110656).length < 2 ^ (prefixWord ++ tailWord_110656).sum := by decide
  have hdescent : baseEnd_110656 < baseStart_110656 := by decide
  rcases family_descends (prefixWord ++ tailWord_110656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110663 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_110663 : Nat := 118140960795 + 110663 * 2 ^ 59
def prefixEnd_110663 : Nat := 4983230072969 + 3 ^ 40 * 110663 * 2
def baseEnd_110663 : Nat := 50509608594316234847623

theorem tailTrace_110663 : CollatzResearch.WordTrace tailWord_110663 prefixEnd_110663 50509608594316234847623 := by
  unfold tailWord_110663
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036211198094325580824643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2690807465396217053883095 4036211198094325580824643)
  ·
    refine ⟨6054316797141488371236965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4036211198094325580824643 6054316797141488371236965)
    ·
      refine ⟨1135184399464029069606931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6054316797141488371236965 1135184399464029069606931)
      ·
        refine ⟨1702776599196043604410397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135184399464029069606931 1702776599196043604410397)
        ·
          refine ⟨638541224698516351653899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1702776599196043604410397 638541224698516351653899)
          ·
            refine ⟨957811837047774527480849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638541224698516351653899 957811837047774527480849)
            ·
              refine ⟨718358877785830895610637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957811837047774527480849 718358877785830895610637)
              ·
                refine ⟨269384579169686585853989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718358877785830895610637 269384579169686585853989)
                ·
                  refine ⟨50509608594316234847623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269384579169686585853989 50509608594316234847623)
                  ·
                    rfl

theorem cell20_110663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_110663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110663 prefixEnd_110663 := by exact prefixLift 110663
  have htrace : WordTrace (prefixWord ++ tailWord_110663) baseStart_110663 baseEnd_110663 := by
    simpa [prefixWord, tailWord_110663, baseEnd_110663] using wordTrace_append hprefix tailTrace_110663
  have hstable : (prefixWord ++ tailWord_110663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110663).length < 2 ^ (prefixWord ++ tailWord_110663).sum := by decide
  have hdescent : baseEnd_110663 < baseStart_110663 := by decide
  rcases family_descends (prefixWord ++ tailWord_110663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110701 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_110701 : Nat := 118140960795 + 110701 * 2 ^ 59
def prefixEnd_110701 : Nat := 4983230072969 + 3 ^ 40 * 110701 * 2
def baseEnd_110701 : Nat := 50526952829756991580801

theorem tailTrace_110701 : CollatzResearch.WordTrace tailWord_110701 prefixEnd_110701 50526952829756991580801 := by
  unfold tailWord_110701
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037597171956658070707957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2691731447971105380471971 4037597171956658070707957)
  ·
    refine ⟨378524734870936694128871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4037597171956658070707957 378524734870936694128871)
    ·
      refine ⟨567787102306405041193307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378524734870936694128871 567787102306405041193307)
      ·
        refine ⟨851680653459607561789961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567787102306405041193307 851680653459607561789961)
        ·
          refine ⟨638760490094705671342471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851680653459607561789961 638760490094705671342471)
          ·
            refine ⟨958140735142058507013707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638760490094705671342471 958140735142058507013707)
            ·
              refine ⟨1437211102713087760520561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958140735142058507013707 1437211102713087760520561)
              ·
                refine ⟨1077908327034815820390421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437211102713087760520561 1077908327034815820390421)
                ·
                  refine ⟨50526952829756991580801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1077908327034815820390421 50526952829756991580801)
                  ·
                    rfl

theorem cell20_110701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_110701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110701 prefixEnd_110701 := by exact prefixLift 110701
  have htrace : WordTrace (prefixWord ++ tailWord_110701) baseStart_110701 baseEnd_110701 := by
    simpa [prefixWord, tailWord_110701, baseEnd_110701] using wordTrace_append hprefix tailTrace_110701
  have hstable : (prefixWord ++ tailWord_110701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110701).length < 2 ^ (prefixWord ++ tailWord_110701).sum := by decide
  have hdescent : baseEnd_110701 < baseStart_110701 := by decide
  rcases family_descends (prefixWord ++ tailWord_110701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110711 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 3]
def baseStart_110711 : Nat := 118140960795 + 110711 * 2 ^ 59
def prefixEnd_110711 : Nat := 4983230072969 + 3 ^ 40 * 110711 * 2
def baseEnd_110711 : Nat := 50531517102241401247427

theorem tailTrace_110711 : CollatzResearch.WordTrace tailWord_110711 prefixEnd_110711 50531517102241401247427 := by
  unfold tailWord_110711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037961901920429778571987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2691974601280286519047991 4037961901920429778571987)
  ·
    refine ⟨6056942852880644667857981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037961901920429778571987 6056942852880644667857981)
    ·
      refine ⟨2271353569830241750446743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6056942852880644667857981 2271353569830241750446743)
      ·
        refine ⟨3407030354745362625670115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271353569830241750446743 3407030354745362625670115)
        ·
          refine ⟨5110545532118043938505173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407030354745362625670115 5110545532118043938505173)
          ·
            refine ⟨119778410909016654808715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5110545532118043938505173 119778410909016654808715)
            ·
              refine ⟨179667616363524982213073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119778410909016654808715 179667616363524982213073)
              ·
                refine ⟨134750712272643736659805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179667616363524982213073 134750712272643736659805)
                ·
                  refine ⟨50531517102241401247427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134750712272643736659805 50531517102241401247427)
                  ·
                    rfl

theorem cell20_110711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_110711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110711 prefixEnd_110711 := by exact prefixLift 110711
  have htrace : WordTrace (prefixWord ++ tailWord_110711) baseStart_110711 baseEnd_110711 := by
    simpa [prefixWord, tailWord_110711, baseEnd_110711] using wordTrace_append hprefix tailTrace_110711
  have hstable : (prefixWord ++ tailWord_110711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110711).length < 2 ^ (prefixWord ++ tailWord_110711).sum := by decide
  have hdescent : baseEnd_110711 < baseStart_110711 := by decide
  rcases family_descends (prefixWord ++ tailWord_110711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110728 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_110728 : Nat := 118140960795 + 110728 * 2 ^ 59
def prefixEnd_110728 : Nat := 4983230072969 + 3 ^ 40 * 110728 * 2
def baseEnd_110728 : Nat := 50539276365464897680691

theorem tailTrace_110728 : CollatzResearch.WordTrace tailWord_110728 prefixEnd_110728 50539276365464897680691 := by
  unfold tailWord_110728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019290971429420840970419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2692387961905894454627225 2019290971429420840970419)
  ·
    refine ⟨3028936457144131261455629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2019290971429420840970419 3028936457144131261455629)
    ·
      refine ⟨1135851171429049223045861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3028936457144131261455629 1135851171429049223045861)
      ·
        refine ⟨212972094642946729321099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1135851171429049223045861 212972094642946729321099)
        ·
          refine ⟨319458141964420093981649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212972094642946729321099 319458141964420093981649)
          ·
            refine ⟨239593606473315070486237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319458141964420093981649 239593606473315070486237)
            ·
              refine ⟨89847602427493151432339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239593606473315070486237 89847602427493151432339)
              ·
                refine ⟨134771403641239727148509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89847602427493151432339 134771403641239727148509)
                ·
                  refine ⟨50539276365464897680691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134771403641239727148509 50539276365464897680691)
                  ·
                    rfl

theorem cell20_110728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_110728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110728 prefixEnd_110728 := by exact prefixLift 110728
  have htrace : WordTrace (prefixWord ++ tailWord_110728) baseStart_110728 baseEnd_110728 := by
    simpa [prefixWord, tailWord_110728, baseEnd_110728] using wordTrace_append hprefix tailTrace_110728
  have hstable : (prefixWord ++ tailWord_110728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110728).length < 2 ^ (prefixWord ++ tailWord_110728).sum := by decide
  have hdescent : baseEnd_110728 < baseStart_110728 := by decide
  rcases family_descends (prefixWord ++ tailWord_110728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110770 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_110770 : Nat := 118140960795 + 110770 * 2 ^ 59
def prefixEnd_110770 : Nat := 4983230072969 + 3 ^ 40 * 110770 * 2
def baseEnd_110770 : Nat := 50558446309899418280519

theorem tailTrace_110770 : CollatzResearch.WordTrace tailWord_110770 prefixEnd_110770 50558446309899418280519 := by
  unfold tailWord_110770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010028452176670713742441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2693409205804455236646509 1010028452176670713742441)
  ·
    refine ⟨757521339132503035306831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1010028452176670713742441 757521339132503035306831)
    ·
      refine ⟨1136282008698754552960247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757521339132503035306831 1136282008698754552960247)
      ·
        refine ⟨1704423013048131829440371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136282008698754552960247 1704423013048131829440371)
        ·
          refine ⟨2556634519572197744160557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704423013048131829440371 2556634519572197744160557)
          ·
            refine ⟨958737944839574154060209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2556634519572197744160557 958737944839574154060209)
            ·
              refine ⟨719053458629680615545157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958737944839574154060209 719053458629680615545157)
              ·
                refine ⟨134822523493065115414717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719053458629680615545157 134822523493065115414717)
                ·
                  refine ⟨50558446309899418280519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134822523493065115414717 50558446309899418280519)
                  ·
                    rfl

theorem cell20_110770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_110770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110770 prefixEnd_110770 := by exact prefixLift 110770
  have htrace : WordTrace (prefixWord ++ tailWord_110770) baseStart_110770 baseEnd_110770 := by
    simpa [prefixWord, tailWord_110770, baseEnd_110770] using wordTrace_append hprefix tailTrace_110770
  have hstable : (prefixWord ++ tailWord_110770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110770).length < 2 ^ (prefixWord ++ tailWord_110770).sum := by decide
  have hdescent : baseEnd_110770 < baseStart_110770 := by decide
  rcases family_descends (prefixWord ++ tailWord_110770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110784 : List Nat := [2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_110784 : Nat := 118140960795 + 110784 * 2 ^ 59
def prefixEnd_110784 : Nat := 4983230072969 + 3 ^ 40 * 110784 * 2
def baseEnd_110784 : Nat := 16854945430459197271265

theorem tailTrace_110784 : CollatzResearch.WordTrace tailWord_110784 prefixEnd_110784 16854945430459197271265 := by
  unfold tailWord_110784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020312215327981622989703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2693749620437308830652937 2020312215327981622989703)
  ·
    refine ⟨3030468322991972434484555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2020312215327981622989703 3030468322991972434484555)
    ·
      refine ⟨4545702484487958651726833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030468322991972434484555 4545702484487958651726833)
      ·
        refine ⟨3409276863365968988795125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4545702484487958651726833 3409276863365968988795125)
        ·
          refine ⟨319619705940559592699543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3409276863365968988795125 319619705940559592699543)
          ·
            refine ⟨479429558910839389049315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319619705940559592699543 479429558910839389049315)
            ·
              refine ⟨719144338366259083573973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479429558910839389049315 719144338366259083573973)
              ·
                refine ⟨16854945430459197271265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 719144338366259083573973 16854945430459197271265)
                ·
                  rfl

theorem cell20_110784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_110784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110784 prefixEnd_110784 := by exact prefixLift 110784
  have htrace : WordTrace (prefixWord ++ tailWord_110784) baseStart_110784 baseEnd_110784 := by
    simpa [prefixWord, tailWord_110784, baseEnd_110784] using wordTrace_append hprefix tailTrace_110784
  have hstable : (prefixWord ++ tailWord_110784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110784).length < 2 ^ (prefixWord ++ tailWord_110784).sum := by decide
  have hdescent : baseEnd_110784 < baseStart_110784 := by decide
  rcases family_descends (prefixWord ++ tailWord_110784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110818 : List Nat := [3, 3, 4, 1, 9]
def baseStart_110818 : Nat := 118140960795 + 110818 * 2 ^ 59
def prefixEnd_110818 : Nat := 4983230072969 + 3 ^ 40 * 110818 * 2
def baseEnd_110818 : Nat := 624448824911414625683

theorem tailTrace_110818 : CollatzResearch.WordTrace tailWord_110818 prefixEnd_110818 624448824911414625683 := by
  unfold tailWord_110818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010466128133196763179277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2694576341688524701811405 1010466128133196763179277)
  ·
    refine ⟨378924798049948786192229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1010466128133196763179277 378924798049948786192229)
    ·
      refine ⟨71048399634365397411043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378924798049948786192229 71048399634365397411043)
      ·
        refine ⟨106572599451548096116565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71048399634365397411043 106572599451548096116565)
        ·
          refine ⟨624448824911414625683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 106572599451548096116565 624448824911414625683)
          ·
            rfl

theorem cell20_110818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 9].length) (baseStart_110818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110818 prefixEnd_110818 := by exact prefixLift 110818
  have htrace : WordTrace (prefixWord ++ tailWord_110818) baseStart_110818 baseEnd_110818 := by
    simpa [prefixWord, tailWord_110818, baseEnd_110818] using wordTrace_append hprefix tailTrace_110818
  have hstable : (prefixWord ++ tailWord_110818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110818).length < 2 ^ (prefixWord ++ tailWord_110818).sum := by decide
  have hdescent : baseEnd_110818 < baseStart_110818 := by decide
  rcases family_descends (prefixWord ++ tailWord_110818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110877 : List Nat := [1, 4, 2, 3, 2, 1, 7]
def baseStart_110877 : Nat := 118140960795 + 110877 * 2 ^ 59
def prefixEnd_110877 : Nat := 4983230072969 + 3 ^ 40 * 110877 * 2
def baseEnd_110877 : Nat := 5623031558386955745935

theorem tailTrace_110877 : CollatzResearch.WordTrace tailWord_110877 prefixEnd_110877 5623031558386955745935 := by
  unfold tailWord_110877
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044016419319040129114885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2696010946212693419409923 4044016419319040129114885)
  ·
    refine ⟨758253078622320024209041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4044016419319040129114885 758253078622320024209041)
    ·
      refine ⟨568689808966740018156781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 758253078622320024209041 568689808966740018156781)
      ·
        refine ⟨213258678362527506808793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568689808966740018156781 213258678362527506808793)
        ·
          refine ⟨159944008771895630106595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213258678362527506808793 159944008771895630106595)
          ·
            refine ⟨239916013157843445159893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159944008771895630106595 239916013157843445159893)
            ·
              refine ⟨5623031558386955745935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239916013157843445159893 5623031558386955745935)
              ·
                rfl

theorem cell20_110877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_110877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110877 prefixEnd_110877 := by exact prefixLift 110877
  have htrace : WordTrace (prefixWord ++ tailWord_110877) baseStart_110877 baseEnd_110877 := by
    simpa [prefixWord, tailWord_110877, baseEnd_110877] using wordTrace_append hprefix tailTrace_110877
  have hstable : (prefixWord ++ tailWord_110877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110877).length < 2 ^ (prefixWord ++ tailWord_110877).sum := by decide
  have hdescent : baseEnd_110877 < baseStart_110877 := by decide
  rcases family_descends (prefixWord ++ tailWord_110877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110884 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_110884 : Nat := 118140960795 + 110884 * 2 ^ 59
def prefixEnd_110884 : Nat := 4983230072969 + 3 ^ 40 * 110884 * 2
def baseEnd_110884 : Nat := 50610479016221688480053

theorem tailTrace_110884 : CollatzResearch.WordTrace tailWord_110884 prefixEnd_110884 50610479016221688480053 := by
  unfold tailWord_110884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022135865146840162309853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2696181153529120216413137 2022135865146840162309853)
  ·
    refine ⟨758300949430065060866195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2022135865146840162309853 758300949430065060866195)
    ·
      refine ⟨1137451424145097591299293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758300949430065060866195 1137451424145097591299293)
      ·
        refine ⟨426544284054411596737235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1137451424145097591299293 426544284054411596737235)
        ·
          refine ⟨639816426081617395105853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426544284054411596737235 639816426081617395105853)
          ·
            refine ⟨239931159780606523164695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639816426081617395105853 239931159780606523164695)
            ·
              refine ⟨359896739670909784747043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239931159780606523164695 359896739670909784747043)
              ·
                refine ⟨539845109506364677120565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359896739670909784747043 539845109506364677120565)
                ·
                  refine ⟨50610479016221688480053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539845109506364677120565 50610479016221688480053)
                  ·
                    rfl

theorem cell20_110884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_110884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110884 prefixEnd_110884 := by exact prefixLift 110884
  have htrace : WordTrace (prefixWord ++ tailWord_110884) baseStart_110884 baseEnd_110884 := by
    simpa [prefixWord, tailWord_110884, baseEnd_110884] using wordTrace_append hprefix tailTrace_110884
  have hstable : (prefixWord ++ tailWord_110884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110884).length < 2 ^ (prefixWord ++ tailWord_110884).sum := by decide
  have hdescent : baseEnd_110884 < baseStart_110884 := by decide
  rcases family_descends (prefixWord ++ tailWord_110884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110901 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 3]
def baseStart_110901 : Nat := 118140960795 + 110901 * 2 ^ 59
def prefixEnd_110901 : Nat := 4983230072969 + 3 ^ 40 * 110901 * 2
def baseEnd_110901 : Nat := 50618238279445184913317

theorem tailTrace_110901 : CollatzResearch.WordTrace tailWord_110901 prefixEnd_110901 50618238279445184913317 := by
  unfold tailWord_110901
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044891771232092227988557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2696594514154728151992371 4044891771232092227988557)
  ·
    refine ⟨1516834414212034585495709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4044891771232092227988557 1516834414212034585495709)
    ·
      refine ⟨568812905329512969560891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1516834414212034585495709 568812905329512969560891)
      ·
        refine ⟨853219357994269454341337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568812905329512969560891 853219357994269454341337)
        ·
          refine ⟨639914518495702090756003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853219357994269454341337 639914518495702090756003)
          ·
            refine ⟨959871777743553136134005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639914518495702090756003 959871777743553136134005)
            ·
              refine ⟨89987979163458106512563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 959871777743553136134005 89987979163458106512563)
              ·
                refine ⟨134981968745187159768845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89987979163458106512563 134981968745187159768845)
                ·
                  refine ⟨50618238279445184913317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134981968745187159768845 50618238279445184913317)
                  ·
                    rfl

theorem cell20_110901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_110901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110901 prefixEnd_110901 := by exact prefixLift 110901
  have htrace : WordTrace (prefixWord ++ tailWord_110901) baseStart_110901 baseEnd_110901 := by
    simpa [prefixWord, tailWord_110901, baseEnd_110901] using wordTrace_append hprefix tailTrace_110901
  have hstable : (prefixWord ++ tailWord_110901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110901).length < 2 ^ (prefixWord ++ tailWord_110901).sum := by decide
  have hdescent : baseEnd_110901 < baseStart_110901 := by decide
  rcases family_descends (prefixWord ++ tailWord_110901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110912 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_110912 : Nat := 118140960795 + 110912 * 2 ^ 59
def prefixEnd_110912 : Nat := 4983230072969 + 3 ^ 40 * 110912 * 2
def baseEnd_110912 : Nat := 50623258979178035546605

theorem tailTrace_110912 : CollatzResearch.WordTrace tailWord_110912 prefixEnd_110912 50623258979178035546605 := by
  unfold tailWord_110912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022646487096120553319495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2696861982794827404425993 2022646487096120553319495)
  ·
    refine ⟨3033969730644180829979243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2022646487096120553319495 3033969730644180829979243)
    ·
      refine ⟨4550954595966271244968865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3033969730644180829979243 4550954595966271244968865)
      ·
        refine ⟨3413215946974703433726649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550954595966271244968865 3413215946974703433726649)
        ·
          refine ⟨2559911960231027575294987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3413215946974703433726649 2559911960231027575294987)
          ·
            refine ⟨3839867940346541362942481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559911960231027575294987 3839867940346541362942481)
            ·
              refine ⟨2879900955259906022206861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839867940346541362942481 2879900955259906022206861)
              ·
                refine ⟨1079962858222464758327573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2879900955259906022206861 1079962858222464758327573)
                ·
                  refine ⟨50623258979178035546605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1079962858222464758327573 50623258979178035546605)
                  ·
                    rfl

theorem cell20_110912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_110912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110912 prefixEnd_110912 := by exact prefixLift 110912
  have htrace : WordTrace (prefixWord ++ tailWord_110912) baseStart_110912 baseEnd_110912 := by
    simpa [prefixWord, tailWord_110912, baseEnd_110912] using wordTrace_append hprefix tailTrace_110912
  have hstable : (prefixWord ++ tailWord_110912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110912).length < 2 ^ (prefixWord ++ tailWord_110912).sum := by decide
  have hdescent : baseEnd_110912 < baseStart_110912 := by decide
  rcases family_descends (prefixWord ++ tailWord_110912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110943 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_110943 : Nat := 118140960795 + 110943 * 2 ^ 59
def prefixEnd_110943 : Nat := 4983230072969 + 3 ^ 40 * 110943 * 2
def baseEnd_110943 : Nat := 50637408223879705513145

theorem tailTrace_110943 : CollatzResearch.WordTrace tailWord_110943 prefixEnd_110943 50637408223879705513145 := by
  unfold tailWord_110943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046423637079933401017483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2697615758053288934011655 4046423637079933401017483)
  ·
    refine ⟨6069635455619900101526225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4046423637079933401017483 6069635455619900101526225)
    ·
      refine ⟨4552226591714925076144669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6069635455619900101526225 4552226591714925076144669)
      ·
        refine ⟨1707084971893096903554251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4552226591714925076144669 1707084971893096903554251)
        ·
          refine ⟨2560627457839645355331377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707084971893096903554251 2560627457839645355331377)
          ·
            refine ⟨1920470593379734016498533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2560627457839645355331377 1920470593379734016498533)
            ·
              refine ⟨360088236258700128093475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1920470593379734016498533 360088236258700128093475)
              ·
                refine ⟨540132354388050192140213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360088236258700128093475 540132354388050192140213)
                ·
                  refine ⟨50637408223879705513145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540132354388050192140213 50637408223879705513145)
                  ·
                    rfl

theorem cell20_110943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_110943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110943 prefixEnd_110943 := by exact prefixLift 110943
  have htrace : WordTrace (prefixWord ++ tailWord_110943) baseStart_110943 baseEnd_110943 := by
    simpa [prefixWord, tailWord_110943, baseEnd_110943] using wordTrace_append hprefix tailTrace_110943
  have hstable : (prefixWord ++ tailWord_110943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110943).length < 2 ^ (prefixWord ++ tailWord_110943).sum := by decide
  have hdescent : baseEnd_110943 < baseStart_110943 := by decide
  rcases family_descends (prefixWord ++ tailWord_110943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110946 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_110946 : Nat := 118140960795 + 110946 * 2 ^ 59
def prefixEnd_110946 : Nat := 4983230072969 + 3 ^ 40 * 110946 * 2
def baseEnd_110946 : Nat := 50638777505625028413133

theorem tailTrace_110946 : CollatzResearch.WordTrace tailWord_110946 prefixEnd_110946 50638777505625028413133 := by
  unfold tailWord_110946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011633264017266228344173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2697688704046043275584461 1011633264017266228344173)
  ·
    refine ⟨379362474006474835629065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1011633264017266228344173 379362474006474835629065)
    ·
      refine ⟨284521855504856126721799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379362474006474835629065 284521855504856126721799)
      ·
        refine ⟨426782783257284190082699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284521855504856126721799 426782783257284190082699)
        ·
          refine ⟨640174174885926285124049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426782783257284190082699 640174174885926285124049)
          ·
            refine ⟨480130631164444713843037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640174174885926285124049 480130631164444713843037)
            ·
              refine ⟨180048986686666767691139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480130631164444713843037 180048986686666767691139)
              ·
                refine ⟨270073480030000151536709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180048986686666767691139 270073480030000151536709)
                ·
                  refine ⟨50638777505625028413133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270073480030000151536709 50638777505625028413133)
                  ·
                    rfl

theorem cell20_110946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_110946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110946 prefixEnd_110946 := by exact prefixLift 110946
  have htrace : WordTrace (prefixWord ++ tailWord_110946) baseStart_110946 baseEnd_110946 := by
    simpa [prefixWord, tailWord_110946, baseEnd_110946] using wordTrace_append hprefix tailTrace_110946
  have hstable : (prefixWord ++ tailWord_110946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110946).length < 2 ^ (prefixWord ++ tailWord_110946).sum := by decide
  have hdescent : baseEnd_110946 < baseStart_110946 := by decide
  rcases family_descends (prefixWord ++ tailWord_110946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110956 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_110956 : Nat := 118140960795 + 110956 * 2 ^ 59
def prefixEnd_110956 : Nat := 4983230072969 + 3 ^ 40 * 110956 * 2
def baseEnd_110956 : Nat := 50643341778109438079759

theorem tailTrace_110956 : CollatzResearch.WordTrace tailWord_110956 prefixEnd_110956 50643341778109438079759 := by
  unfold tailWord_110956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023448893016418310620361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2697931857355224414160481 2023448893016418310620361)
  ·
    refine ⟨1517586669762313732965271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023448893016418310620361 1517586669762313732965271)
    ·
      refine ⟨2276380004643470599447907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517586669762313732965271 2276380004643470599447907)
      ·
        refine ⟨3414570006965205899171861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276380004643470599447907 3414570006965205899171861)
        ·
          refine ⟨160057969076494026523681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3414570006965205899171861 160057969076494026523681)
          ·
            refine ⟨120043476807370519892761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160057969076494026523681 120043476807370519892761)
            ·
              refine ⟨90032607605527889919571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120043476807370519892761 90032607605527889919571)
              ·
                refine ⟨135048911408291834879357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90032607605527889919571 135048911408291834879357)
                ·
                  refine ⟨50643341778109438079759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135048911408291834879357 50643341778109438079759)
                  ·
                    rfl

theorem cell20_110956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_110956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110956 prefixEnd_110956 := by exact prefixLift 110956
  have htrace : WordTrace (prefixWord ++ tailWord_110956) baseStart_110956 baseEnd_110956 := by
    simpa [prefixWord, tailWord_110956, baseEnd_110956] using wordTrace_append hprefix tailTrace_110956
  have hstable : (prefixWord ++ tailWord_110956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110956).length < 2 ^ (prefixWord ++ tailWord_110956).sum := by decide
  have hdescent : baseEnd_110956 < baseStart_110956 := by decide
  rcases family_descends (prefixWord ++ tailWord_110956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110960 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_110960 : Nat := 118140960795 + 110960 * 2 ^ 59
def prefixEnd_110960 : Nat := 4983230072969 + 3 ^ 40 * 110960 * 2
def baseEnd_110960 : Nat := 50645167487103201946409

theorem tailTrace_110960 : CollatzResearch.WordTrace tailWord_110960 prefixEnd_110960 50645167487103201946409 := by
  unfold tailWord_110960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023521839009172652193167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2698029118678896869590889 2023521839009172652193167)
  ·
    refine ⟨3035282758513758978289751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023521839009172652193167 3035282758513758978289751)
    ·
      refine ⟨4552924137770638467434627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035282758513758978289751 4552924137770638467434627)
      ·
        refine ⟨6829386206655957701151941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552924137770638467434627 6829386206655957701151941)
        ·
          refine ⟨1280509913747992068965989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6829386206655957701151941 1280509913747992068965989)
          ·
            refine ⟨240095608827748512931123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1280509913747992068965989 240095608827748512931123)
            ·
              refine ⟨360143413241622769396685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240095608827748512931123 360143413241622769396685)
              ·
                refine ⟨135053779965608538523757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360143413241622769396685 135053779965608538523757)
                ·
                  refine ⟨50645167487103201946409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135053779965608538523757 50645167487103201946409)
                  ·
                    rfl

theorem cell20_110960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_110960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110960 prefixEnd_110960 := by exact prefixLift 110960
  have htrace : WordTrace (prefixWord ++ tailWord_110960) baseStart_110960 baseEnd_110960 := by
    simpa [prefixWord, tailWord_110960, baseEnd_110960] using wordTrace_append hprefix tailTrace_110960
  have hstable : (prefixWord ++ tailWord_110960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110960).length < 2 ^ (prefixWord ++ tailWord_110960).sum := by decide
  have hdescent : baseEnd_110960 < baseStart_110960 := by decide
  rcases family_descends (prefixWord ++ tailWord_110960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110984 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 2]
def baseStart_110984 : Nat := 118140960795 + 110984 * 2 ^ 59
def prefixEnd_110984 : Nat := 4983230072969 + 3 ^ 40 * 110984 * 2
def baseEnd_110984 : Nat := 50656121741065785146311

theorem tailTrace_110984 : CollatzResearch.WordTrace tailWord_110984 prefixEnd_110984 50656121741065785146311 := by
  unfold tailWord_110984
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023959514965698701630003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2698612686620931602173337 2023959514965698701630003)
  ·
    refine ⟨3035939272448548052445005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023959514965698701630003 3035939272448548052445005)
    ·
      refine ⟨1138477227168205519666877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3035939272448548052445005 1138477227168205519666877)
      ·
        refine ⟨426928960188077069875079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1138477227168205519666877 426928960188077069875079)
        ·
          refine ⟨640393440282115604812619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426928960188077069875079 640393440282115604812619)
          ·
            refine ⟨960590160423173407218929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640393440282115604812619 960590160423173407218929)
            ·
              refine ⟨720442620317380055414197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960590160423173407218929 720442620317380055414197)
              ·
                refine ⟨67541495654754380195081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720442620317380055414197 67541495654754380195081)
                ·
                  refine ⟨50656121741065785146311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67541495654754380195081 50656121741065785146311)
                  ·
                    rfl

theorem cell20_110984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_110984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_110984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_110984 prefixEnd_110984 := by exact prefixLift 110984
  have htrace : WordTrace (prefixWord ++ tailWord_110984) baseStart_110984 baseEnd_110984 := by
    simpa [prefixWord, tailWord_110984, baseEnd_110984] using wordTrace_append hprefix tailTrace_110984
  have hstable : (prefixWord ++ tailWord_110984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110984).length < 2 ^ (prefixWord ++ tailWord_110984).sum := by decide
  have hdescent : baseEnd_110984 < baseStart_110984 := by decide
  rcases family_descends (prefixWord ++ tailWord_110984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111012 : List Nat := [2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_111012 : Nat := 118140960795 + 111012 * 2 ^ 59
def prefixEnd_111012 : Nat := 4983230072969 + 3 ^ 40 * 111012 * 2
def baseEnd_111012 : Nat := 16889633901340710737621

theorem tailTrace_111012 : CollatzResearch.WordTrace tailWord_111012 prefixEnd_111012 16889633901340710737621 := by
  unfold tailWord_111012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024470136914979092639645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2699293515886638790186193 2024470136914979092639645)
  ·
    refine ⟨759176301343117159739867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2024470136914979092639645 759176301343117159739867)
    ·
      refine ⟨1138764452014675739609801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759176301343117159739867 1138764452014675739609801)
      ·
        refine ⟨854073339011006804707351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138764452014675739609801 854073339011006804707351)
        ·
          refine ⟨1281110008516510207061027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854073339011006804707351 1281110008516510207061027)
          ·
            refine ⟨1921665012774765310591541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281110008516510207061027 1921665012774765310591541)
            ·
              refine ⟨180156094947634247867957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1921665012774765310591541 180156094947634247867957)
              ·
                refine ⟨16889633901340710737621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180156094947634247867957 16889633901340710737621)
                ·
                  rfl

theorem cell20_111012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_111012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111012 prefixEnd_111012 := by exact prefixLift 111012
  have htrace : WordTrace (prefixWord ++ tailWord_111012) baseStart_111012 baseEnd_111012 := by
    simpa [prefixWord, tailWord_111012, baseEnd_111012] using wordTrace_append hprefix tailTrace_111012
  have hstable : (prefixWord ++ tailWord_111012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111012).length < 2 ^ (prefixWord ++ tailWord_111012).sum := by decide
  have hdescent : baseEnd_111012 < baseStart_111012 := by decide
  rcases family_descends (prefixWord ++ tailWord_111012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111018 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_111018 : Nat := 118140960795 + 111018 * 2 ^ 59
def prefixEnd_111018 : Nat := 4983230072969 + 3 ^ 40 * 111018 * 2
def baseEnd_111018 : Nat := 50671640267512778012839

theorem tailTrace_111018 : CollatzResearch.WordTrace tailWord_111018 prefixEnd_111018 50671640267512778012839 := by
  unfold tailWord_111018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012289777952055302499427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2699439407872147473331805 1012289777952055302499427)
  ·
    refine ⟨1518434666928082953749141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012289777952055302499427 1518434666928082953749141)
    ·
      refine ⟨71176625012253888456991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1518434666928082953749141 71176625012253888456991)
      ·
        refine ⟨106764937518380832685487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71176625012253888456991 106764937518380832685487)
        ·
          refine ⟨160147406277571249028231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106764937518380832685487 160147406277571249028231)
          ·
            refine ⟨240221109416356873542347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160147406277571249028231 240221109416356873542347)
            ·
              refine ⟨360331664124535310313521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240221109416356873542347 360331664124535310313521)
              ·
                refine ⟨270248748093401482735141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360331664124535310313521 270248748093401482735141)
                ·
                  refine ⟨50671640267512778012839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270248748093401482735141 50671640267512778012839)
                  ·
                    rfl

theorem cell20_111018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_111018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111018 prefixEnd_111018 := by exact prefixLift 111018
  have htrace : WordTrace (prefixWord ++ tailWord_111018) baseStart_111018 baseEnd_111018 := by
    simpa [prefixWord, tailWord_111018, baseEnd_111018] using wordTrace_append hprefix tailTrace_111018
  have hstable : (prefixWord ++ tailWord_111018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111018).length < 2 ^ (prefixWord ++ tailWord_111018).sum := by decide
  have hdescent : baseEnd_111018 < baseStart_111018 := by decide
  rcases family_descends (prefixWord ++ tailWord_111018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111060 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_111060 : Nat := 118140960795 + 111060 * 2 ^ 59
def prefixEnd_111060 : Nat := 4983230072969 + 3 ^ 40 * 111060 * 2
def baseEnd_111060 : Nat := 50690810211947298612667

theorem tailTrace_111060 : CollatzResearch.WordTrace tailWord_111060 prefixEnd_111060 50690810211947298612667 := by
  unfold tailWord_111060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025345488828031191513317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2700460651770708255351089 2025345488828031191513317)
  ·
    refine ⟨379752279155255848408747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2025345488828031191513317 379752279155255848408747)
    ·
      refine ⟨569628418732883772613121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379752279155255848408747 569628418732883772613121)
      ·
        refine ⟨427221314049662829459841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569628418732883772613121 427221314049662829459841)
        ·
          refine ⟨320415985537247122094881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427221314049662829459841 320415985537247122094881)
          ·
            refine ⟨240311989152935341571161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320415985537247122094881 240311989152935341571161)
            ·
              refine ⟨180233991864701506178371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240311989152935341571161 180233991864701506178371)
              ·
                refine ⟨270350987797052259267557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180233991864701506178371 270350987797052259267557)
                ·
                  refine ⟨50690810211947298612667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270350987797052259267557 50690810211947298612667)
                  ·
                    rfl

theorem cell20_111060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_111060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111060 prefixEnd_111060 := by exact prefixLift 111060
  have htrace : WordTrace (prefixWord ++ tailWord_111060) baseStart_111060 baseEnd_111060 := by
    simpa [prefixWord, tailWord_111060, baseEnd_111060] using wordTrace_append hprefix tailTrace_111060
  have hstable : (prefixWord ++ tailWord_111060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111060).length < 2 ^ (prefixWord ++ tailWord_111060).sum := by decide
  have hdescent : baseEnd_111060 < baseStart_111060 := by decide
  rcases family_descends (prefixWord ++ tailWord_111060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111109 : List Nat := [1, 3, 1, 1, 2, 2, 10]
def baseStart_111109 : Nat := 118140960795 + 111109 * 2 ^ 59
def prefixEnd_111109 : Nat := 4983230072969 + 3 ^ 40 * 111109 * 2
def baseEnd_111109 : Nat := 5634797238568989553237

theorem tailTrace_111109 : CollatzResearch.WordTrace tailWord_111109 prefixEnd_111109 5634797238568989553237 := by
  unfold tailWord_111109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052478154478543751560381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2701652102985695834373587 4052478154478543751560381)
  ·
    refine ⟨1519679307929453906835143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4052478154478543751560381 1519679307929453906835143)
    ·
      refine ⟨2279518961894180860252715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519679307929453906835143 2279518961894180860252715)
      ·
        refine ⟨3419278442841271290379073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279518961894180860252715 3419278442841271290379073)
        ·
          refine ⟨2564458832130953467784305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419278442841271290379073 2564458832130953467784305)
          ·
            refine ⟨1923344124098215100838229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564458832130953467784305 1923344124098215100838229)
            ·
              refine ⟨5634797238568989553237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1923344124098215100838229 5634797238568989553237)
              ·
                rfl

theorem cell20_111109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_111109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111109 prefixEnd_111109 := by exact prefixLift 111109
  have htrace : WordTrace (prefixWord ++ tailWord_111109) baseStart_111109 baseEnd_111109 := by
    simpa [prefixWord, tailWord_111109, baseEnd_111109] using wordTrace_append hprefix tailTrace_111109
  have hstable : (prefixWord ++ tailWord_111109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111109).length < 2 ^ (prefixWord ++ tailWord_111109).sum := by decide
  have hdescent : baseEnd_111109 < baseStart_111109 := by decide
  rcases family_descends (prefixWord ++ tailWord_111109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111115 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 2]
def baseStart_111115 : Nat := 118140960795 + 111115 * 2 ^ 59
def prefixEnd_111115 : Nat := 4983230072969 + 3 ^ 40 * 111115 * 2
def baseEnd_111115 : Nat := 50715913710611551779109

theorem tailTrace_111115 : CollatzResearch.WordTrace tailWord_111115 prefixEnd_111115 50715913710611551779109 := by
  unfold tailWord_111115
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052696992456806776278799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2701797994971204517519199 4052696992456806776278799)
  ·
    refine ⟨6079045488685210164418199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4052696992456806776278799 6079045488685210164418199)
    ·
      refine ⟨9118568233027815246627299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079045488685210164418199 9118568233027815246627299)
      ·
        refine ⟨13677852349541722869940949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118568233027815246627299 13677852349541722869940949)
        ·
          refine ⟨320574664442384129764241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13677852349541722869940949 320574664442384129764241)
          ·
            refine ⟨240430998331788097323181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320574664442384129764241 240430998331788097323181)
            ·
              refine ⟨90161624374420536496193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240430998331788097323181 90161624374420536496193)
              ·
                refine ⟨67621218280815402372145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90161624374420536496193 67621218280815402372145)
                ·
                  refine ⟨50715913710611551779109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67621218280815402372145 50715913710611551779109)
                  ·
                    rfl

theorem cell20_111115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 2].length) (baseStart_111115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111115 prefixEnd_111115 := by exact prefixLift 111115
  have htrace : WordTrace (prefixWord ++ tailWord_111115) baseStart_111115 baseEnd_111115 := by
    simpa [prefixWord, tailWord_111115, baseEnd_111115] using wordTrace_append hprefix tailTrace_111115
  have hstable : (prefixWord ++ tailWord_111115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111115).length < 2 ^ (prefixWord ++ tailWord_111115).sum := by decide
  have hdescent : baseEnd_111115 < baseStart_111115 := by decide
  rcases family_descends (prefixWord ++ tailWord_111115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111166 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_111166 : Nat := 118140960795 + 111166 * 2 ^ 59
def prefixEnd_111166 : Nat := 4983230072969 + 3 ^ 40 * 111166 * 2
def baseEnd_111166 : Nat := 50739191500282041078901

theorem tailTrace_111166 : CollatzResearch.WordTrace tailWord_111166 prefixEnd_111166 50739191500282041078901 := by
  unfold tailWord_111166
  simp only [CollatzResearch.WordTrace]
  refine ⟨506819639409005310798169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2703038076848028324256901 506819639409005310798169)
  ·
    refine ⟨380114729556753983098627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 506819639409005310798169 380114729556753983098627)
    ·
      refine ⟨570172094335130974647941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380114729556753983098627 570172094335130974647941)
      ·
        refine ⟨106907267687837057746489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 570172094335130974647941 106907267687837057746489)
        ·
          refine ⟨80180450765877793309867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106907267687837057746489 80180450765877793309867)
          ·
            refine ⟨120270676148816689964801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80180450765877793309867 120270676148816689964801)
            ·
              refine ⟨90203007111612517473601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120270676148816689964801 90203007111612517473601)
              ·
                refine ⟨67652255333709388105201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90203007111612517473601 67652255333709388105201)
                ·
                  refine ⟨50739191500282041078901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67652255333709388105201 50739191500282041078901)
                  ·
                    rfl

theorem cell20_111166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_111166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111166 prefixEnd_111166 := by exact prefixLift 111166
  have htrace : WordTrace (prefixWord ++ tailWord_111166) baseStart_111166 baseEnd_111166 := by
    simpa [prefixWord, tailWord_111166, baseEnd_111166] using wordTrace_append hprefix tailTrace_111166
  have hstable : (prefixWord ++ tailWord_111166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111166).length < 2 ^ (prefixWord ++ tailWord_111166).sum := by decide
  have hdescent : baseEnd_111166 < baseStart_111166 := by decide
  rcases family_descends (prefixWord ++ tailWord_111166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111181 : List Nat := [1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_111181 : Nat := 118140960795 + 111181 * 2 ^ 59
def prefixEnd_111181 : Nat := 4983230072969 + 3 ^ 40 * 111181 * 2
def baseEnd_111181 : Nat := 16915345969669551859613

theorem tailTrace_111181 : CollatzResearch.WordTrace tailWord_111181 prefixEnd_111181 16915345969669551859613 := by
  unfold tailWord_111181
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055104210217700048181397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2703402806811800032120931 4055104210217700048181397)
  ·
    refine ⟨190083009853954689758503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4055104210217700048181397 190083009853954689758503)
    ·
      refine ⟨285124514780932034637755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190083009853954689758503 285124514780932034637755)
      ·
        refine ⟨427686772171398051956633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285124514780932034637755 427686772171398051956633)
        ·
          refine ⟨320765079128548538967475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427686772171398051956633 320765079128548538967475)
          ·
            refine ⟨481147618692822808451213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320765079128548538967475 481147618692822808451213)
            ·
              refine ⟨180430357009808553169205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481147618692822808451213 180430357009808553169205)
              ·
                refine ⟨16915345969669551859613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180430357009808553169205 16915345969669551859613)
                ·
                  rfl

theorem cell20_111181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_111181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111181 prefixEnd_111181 := by exact prefixLift 111181
  have htrace : WordTrace (prefixWord ++ tailWord_111181) baseStart_111181 baseEnd_111181 := by
    simpa [prefixWord, tailWord_111181, baseEnd_111181] using wordTrace_append hprefix tailTrace_111181
  have hstable : (prefixWord ++ tailWord_111181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111181).length < 2 ^ (prefixWord ++ tailWord_111181).sum := by decide
  have hdescent : baseEnd_111181 < baseStart_111181 := by decide
  rcases family_descends (prefixWord ++ tailWord_111181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111188 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_111188 : Nat := 118140960795 + 111188 * 2 ^ 59
def prefixEnd_111188 : Nat := 4983230072969 + 3 ^ 40 * 111188 * 2
def baseEnd_111188 : Nat := 50749232899747742345477

theorem tailTrace_111188 : CollatzResearch.WordTrace tailWord_111188 prefixEnd_111188 50749232899747742345477 := by
  unfold tailWord_111188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027679760596170121843109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2703573014128226829124145 2027679760596170121843109)
  ·
    refine ⟨380189955111781897845583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2027679760596170121843109 380189955111781897845583)
    ·
      refine ⟨570284932667672846768375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380189955111781897845583 570284932667672846768375)
      ·
        refine ⟨855427399001509270152563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570284932667672846768375 855427399001509270152563)
        ·
          refine ⟨1283141098502263905228845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855427399001509270152563 1283141098502263905228845)
          ·
            refine ⟨481177911938348964460817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1283141098502263905228845 481177911938348964460817)
            ·
              refine ⟨360883433953761723345613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481177911938348964460817 360883433953761723345613)
              ·
                refine ⟨135331287732660646254605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360883433953761723345613 135331287732660646254605)
                ·
                  refine ⟨50749232899747742345477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135331287732660646254605 50749232899747742345477)
                  ·
                    rfl

theorem cell20_111188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_111188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111188 prefixEnd_111188 := by exact prefixLift 111188
  have htrace : WordTrace (prefixWord ++ tailWord_111188) baseStart_111188 baseEnd_111188 := by
    simpa [prefixWord, tailWord_111188, baseEnd_111188] using wordTrace_append hprefix tailTrace_111188
  have hstable : (prefixWord ++ tailWord_111188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111188).length < 2 ^ (prefixWord ++ tailWord_111188).sum := by decide
  have hdescent : baseEnd_111188 < baseStart_111188 := by decide
  rcases family_descends (prefixWord ++ tailWord_111188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111222 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_111222 : Nat := 118140960795 + 111222 * 2 ^ 59
def prefixEnd_111222 : Nat := 4983230072969 + 3 ^ 40 * 111222 * 2
def baseEnd_111222 : Nat := 50764751426194735212005

theorem tailTrace_111222 : CollatzResearch.WordTrace tailWord_111222 prefixEnd_111222 50764751426194735212005 := by
  unfold tailWord_111222
  simp only [CollatzResearch.WordTrace]
  refine ⟨253537475191822753151495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2704399735379442700282613 253537475191822753151495)
  ·
    refine ⟨380306212787734129727243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253537475191822753151495 380306212787734129727243)
    ·
      refine ⟨570459319181601194590865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380306212787734129727243 570459319181601194590865)
      ·
        refine ⟨427844489386200895943149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570459319181601194590865 427844489386200895943149)
        ·
          refine ⟨160441683519825335978681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427844489386200895943149 160441683519825335978681)
          ·
            refine ⟨120331262639869001984011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160441683519825335978681 120331262639869001984011)
            ·
              refine ⟨180496893959803502976017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120331262639869001984011 180496893959803502976017)
              ·
                refine ⟨135372670469852627232013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180496893959803502976017 135372670469852627232013)
                ·
                  refine ⟨50764751426194735212005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135372670469852627232013 50764751426194735212005)
                  ·
                    rfl

theorem cell20_111222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_111222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111222 prefixEnd_111222 := by exact prefixLift 111222
  have htrace : WordTrace (prefixWord ++ tailWord_111222) baseStart_111222 baseEnd_111222 := by
    simpa [prefixWord, tailWord_111222, baseEnd_111222] using wordTrace_append hprefix tailTrace_111222
  have hstable : (prefixWord ++ tailWord_111222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111222).length < 2 ^ (prefixWord ++ tailWord_111222).sum := by decide
  have hdescent : baseEnd_111222 < baseStart_111222 := by decide
  rcases family_descends (prefixWord ++ tailWord_111222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111233 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_111233 : Nat := 118140960795 + 111233 * 2 ^ 59
def prefixEnd_111233 : Nat := 4983230072969 + 3 ^ 40 * 111233 * 2
def baseEnd_111233 : Nat := 50769772125927585845293

theorem tailTrace_111233 : CollatzResearch.WordTrace tailWord_111233 prefixEnd_111233 50769772125927585845293 := by
  unfold tailWord_111233
  simp only [CollatzResearch.WordTrace]
  refine ⟨4057000806029312929074353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2704667204019541952716235 4057000806029312929074353)
  ·
    refine ⟨3042750604521984696805765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4057000806029312929074353 3042750604521984696805765)
    ·
      refine ⟨570515738347872130651081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3042750604521984696805765 570515738347872130651081)
      ·
        refine ⟨427886803760904097988311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570515738347872130651081 427886803760904097988311)
        ·
          refine ⟨641830205641356146982467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427886803760904097988311 641830205641356146982467)
          ·
            refine ⟨962745308462034220473701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641830205641356146982467 962745308462034220473701)
            ·
              refine ⟨180514745336631416338819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 962745308462034220473701 180514745336631416338819)
              ·
                refine ⟨270772118004947124508229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180514745336631416338819 270772118004947124508229)
                ·
                  refine ⟨50769772125927585845293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270772118004947124508229 50769772125927585845293)
                  ·
                    rfl

theorem cell20_111233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_111233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111233 prefixEnd_111233 := by exact prefixLift 111233
  have htrace : WordTrace (prefixWord ++ tailWord_111233) baseStart_111233 baseEnd_111233 := by
    simpa [prefixWord, tailWord_111233, baseEnd_111233] using wordTrace_append hprefix tailTrace_111233
  have hstable : (prefixWord ++ tailWord_111233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111233).length < 2 ^ (prefixWord ++ tailWord_111233).sum := by decide
  have hdescent : baseEnd_111233 < baseStart_111233 := by decide
  rcases family_descends (prefixWord ++ tailWord_111233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111274 : List Nat := [3, 1, 5, 2, 1, 2, 6]
def baseStart_111274 : Nat := 118140960795 + 111274 * 2 ^ 59
def prefixEnd_111274 : Nat := 4983230072969 + 3 ^ 40 * 111274 * 2
def baseEnd_111274 : Nat := 5643165071457073942051

theorem tailTrace_111274 : CollatzResearch.WordTrace tailWord_111274 prefixEnd_111274 5643165071457073942051 := by
  unfold tailWord_111274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014624049720194232829219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2705664132587184620877917 1014624049720194232829219)
  ·
    refine ⟨1521936074580291349243829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1014624049720194232829219 1521936074580291349243829)
    ·
      refine ⟨142681506991902313991609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1521936074580291349243829 142681506991902313991609)
      ·
        refine ⟨107011130243926735493707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142681506991902313991609 107011130243926735493707)
        ·
          refine ⟨160516695365890103240561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107011130243926735493707 160516695365890103240561)
          ·
            refine ⟨120387521524417577430421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160516695365890103240561 120387521524417577430421)
            ·
              refine ⟨5643165071457073942051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120387521524417577430421 5643165071457073942051)
              ·
                rfl

theorem cell20_111274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 6].length) (baseStart_111274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111274 prefixEnd_111274 := by exact prefixLift 111274
  have htrace : WordTrace (prefixWord ++ tailWord_111274) baseStart_111274 baseEnd_111274 := by
    simpa [prefixWord, tailWord_111274, baseEnd_111274] using wordTrace_append hprefix tailTrace_111274
  have hstable : (prefixWord ++ tailWord_111274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111274).length < 2 ^ (prefixWord ++ tailWord_111274).sum := by decide
  have hdescent : baseEnd_111274 < baseStart_111274 := by decide
  rcases family_descends (prefixWord ++ tailWord_111274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111343 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 2]
def baseStart_111343 : Nat := 118140960795 + 111343 * 2 ^ 59
def prefixEnd_111343 : Nat := 4983230072969 + 3 ^ 40 * 111343 * 2
def baseEnd_111343 : Nat := 50819979123256092178177

theorem tailTrace_111343 : CollatzResearch.WordTrace tailWord_111343 prefixEnd_111343 50819979123256092178177 := by
  unfold tailWord_111343
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061012835630801715578683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2707341890420534477052455 4061012835630801715578683)
  ·
    refine ⟨6091519253446202573368025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061012835630801715578683 6091519253446202573368025)
    ·
      refine ⟨4568639440084651930026019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6091519253446202573368025 4568639440084651930026019)
      ·
        refine ⟨6852959160126977895039029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568639440084651930026019 6852959160126977895039029)
        ·
          refine ⟨642464921261904177659909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6852959160126977895039029 642464921261904177659909)
          ·
            refine ⟨120462172736607033311233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 642464921261904177659909 120462172736607033311233)
            ·
              refine ⟨90346629552455274983425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120462172736607033311233 90346629552455274983425)
              ·
                refine ⟨67759972164341456237569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90346629552455274983425 67759972164341456237569)
                ·
                  refine ⟨50819979123256092178177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67759972164341456237569 50819979123256092178177)
                  ·
                    rfl

theorem cell20_111343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 2].length) (baseStart_111343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111343 prefixEnd_111343 := by exact prefixLift 111343
  have htrace : WordTrace (prefixWord ++ tailWord_111343) baseStart_111343 baseEnd_111343 := by
    simpa [prefixWord, tailWord_111343, baseEnd_111343] using wordTrace_append hprefix tailTrace_111343
  have hstable : (prefixWord ++ tailWord_111343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111343).length < 2 ^ (prefixWord ++ tailWord_111343).sum := by decide
  have hdescent : baseEnd_111343 < baseStart_111343 := by decide
  rcases family_descends (prefixWord ++ tailWord_111343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111368 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_111368 : Nat := 118140960795 + 111368 * 2 ^ 59
def prefixEnd_111368 : Nat := 4983230072969 + 3 ^ 40 * 111368 * 2
def baseEnd_111368 : Nat := 50831389804467116344741

theorem tailTrace_111368 : CollatzResearch.WordTrace tailWord_111368 prefixEnd_111368 50831389804467116344741 := by
  unfold tailWord_111368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030962330270115492619379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2707949773693487323492505 2030962330270115492619379)
  ·
    refine ⟨3046443495405173238929069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030962330270115492619379 3046443495405173238929069)
    ·
      refine ⟨1142416310776939964598401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3046443495405173238929069 1142416310776939964598401)
      ·
        refine ⟨856812233082704973448801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142416310776939964598401 856812233082704973448801)
        ·
          refine ⟨642609174812028730086601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856812233082704973448801 642609174812028730086601)
          ·
            refine ⟨481956881109021547564951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642609174812028730086601 481956881109021547564951)
            ·
              refine ⟨722935321663532321347427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481956881109021547564951 722935321663532321347427)
              ·
                refine ⟨1084402982495298482021141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722935321663532321347427 1084402982495298482021141)
                ·
                  refine ⟨50831389804467116344741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1084402982495298482021141 50831389804467116344741)
                  ·
                    rfl

theorem cell20_111368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_111368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111368 prefixEnd_111368 := by exact prefixLift 111368
  have htrace : WordTrace (prefixWord ++ tailWord_111368) baseStart_111368 baseEnd_111368 := by
    simpa [prefixWord, tailWord_111368, baseEnd_111368] using wordTrace_append hprefix tailTrace_111368
  have hstable : (prefixWord ++ tailWord_111368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111368).length < 2 ^ (prefixWord ++ tailWord_111368).sum := by decide
  have hdescent : baseEnd_111368 < baseStart_111368 := by decide
  rcases family_descends (prefixWord ++ tailWord_111368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111412 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_111412 : Nat := 118140960795 + 111412 * 2 ^ 59
def prefixEnd_111412 : Nat := 4983230072969 + 3 ^ 40 * 111412 * 2
def baseEnd_111412 : Nat := 50851472603398518877895

theorem tailTrace_111412 : CollatzResearch.WordTrace tailWord_111412 prefixEnd_111412 50851472603398518877895 := by
  unfold tailWord_111412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031764736190413249920245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2709019648253884333226993 2031764736190413249920245)
  ·
    refine ⟨190477944017851242180023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2031764736190413249920245 190477944017851242180023)
    ·
      refine ⟨285716916026776863270035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190477944017851242180023 285716916026776863270035)
      ·
        refine ⟨428575374040165294905053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285716916026776863270035 428575374040165294905053)
        ·
          refine ⟨160715765265061985589395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428575374040165294905053 160715765265061985589395)
          ·
            refine ⟨241073647897592978384093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160715765265061985589395 241073647897592978384093)
            ·
              refine ⟨90402617961597366894035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241073647897592978384093 90402617961597366894035)
              ·
                refine ⟨135603926942396050341053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90402617961597366894035 135603926942396050341053)
                ·
                  refine ⟨50851472603398518877895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135603926942396050341053 50851472603398518877895)
                  ·
                    rfl

theorem cell20_111412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_111412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111412 prefixEnd_111412 := by exact prefixLift 111412
  have htrace : WordTrace (prefixWord ++ tailWord_111412) baseStart_111412 baseEnd_111412 := by
    simpa [prefixWord, tailWord_111412, baseEnd_111412] using wordTrace_append hprefix tailTrace_111412
  have hstable : (prefixWord ++ tailWord_111412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111412).length < 2 ^ (prefixWord ++ tailWord_111412).sum := by decide
  have hdescent : baseEnd_111412 < baseStart_111412 := by decide
  rcases family_descends (prefixWord ++ tailWord_111412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111416 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_111416 : Nat := 118140960795 + 111416 * 2 ^ 59
def prefixEnd_111416 : Nat := 4983230072969 + 3 ^ 40 * 111416 * 2
def baseEnd_111416 : Nat := 50853298312392282744545

theorem tailTrace_111416 : CollatzResearch.WordTrace tailWord_111416 prefixEnd_111416 50853298312392282744545 := by
  unfold tailWord_111416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031837682183167591493051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2709116909577556788657401 2031837682183167591493051)
  ·
    refine ⟨3047756523274751387239577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031837682183167591493051 3047756523274751387239577)
    ·
      refine ⟨2285817392456063540429683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3047756523274751387239577 2285817392456063540429683)
      ·
        refine ⟨3428726088684095310644525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2285817392456063540429683 3428726088684095310644525)
        ·
          refine ⟨1285772283256535741491697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3428726088684095310644525 1285772283256535741491697)
          ·
            refine ⟨964329212442401806118773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285772283256535741491697 964329212442401806118773)
            ·
              refine ⟨90405863666475169323635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 964329212442401806118773 90405863666475169323635)
              ·
                refine ⟨135608795499712753985453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90405863666475169323635 135608795499712753985453)
                ·
                  refine ⟨50853298312392282744545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135608795499712753985453 50853298312392282744545)
                  ·
                    rfl

theorem cell20_111416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_111416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111416 prefixEnd_111416 := by exact prefixLift 111416
  have htrace : WordTrace (prefixWord ++ tailWord_111416) baseStart_111416 baseEnd_111416 := by
    simpa [prefixWord, tailWord_111416, baseEnd_111416] using wordTrace_append hprefix tailTrace_111416
  have hstable : (prefixWord ++ tailWord_111416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111416).length < 2 ^ (prefixWord ++ tailWord_111416).sum := by decide
  have hdescent : baseEnd_111416 < baseStart_111416 := by decide
  rcases family_descends (prefixWord ++ tailWord_111416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111461 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 2]
def baseStart_111461 : Nat := 118140960795 + 111461 * 2 ^ 59
def prefixEnd_111461 : Nat := 4983230072969 + 3 ^ 40 * 111461 * 2
def baseEnd_111461 : Nat := 50873837538572126244361

theorem tailTrace_111461 : CollatzResearch.WordTrace tailWord_111461 prefixEnd_111461 50873837538572126244361 := by
  unfold tailWord_111461
  simp only [CollatzResearch.WordTrace]
  refine ⟨4065316649203307868374237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2710211099468871912249491 4065316649203307868374237)
  ·
    refine ⟨1524493743451240450640339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4065316649203307868374237 1524493743451240450640339)
    ·
      refine ⟨2286740615176860675960509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524493743451240450640339 2286740615176860675960509)
      ·
        refine ⟨857527730691322753485191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2286740615176860675960509 857527730691322753485191)
        ·
          refine ⟨1286291596036984130227787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857527730691322753485191 1286291596036984130227787)
          ·
            refine ⟨1929437394055476195341681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286291596036984130227787 1929437394055476195341681)
            ·
              refine ⟨1447078045541607146506261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929437394055476195341681 1447078045541607146506261)
              ·
                refine ⟨67831783384762834992481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1447078045541607146506261 67831783384762834992481)
                ·
                  refine ⟨50873837538572126244361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67831783384762834992481 50873837538572126244361)
                  ·
                    rfl

theorem cell20_111461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_111461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111461 prefixEnd_111461 := by exact prefixLift 111461
  have htrace : WordTrace (prefixWord ++ tailWord_111461) baseStart_111461 baseEnd_111461 := by
    simpa [prefixWord, tailWord_111461, baseEnd_111461] using wordTrace_append hprefix tailTrace_111461
  have hstable : (prefixWord ++ tailWord_111461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111461).length < 2 ^ (prefixWord ++ tailWord_111461).sum := by decide
  have hdescent : baseEnd_111461 < baseStart_111461 := by decide
  rcases family_descends (prefixWord ++ tailWord_111461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111506 : List Nat := [3, 2, 3, 2, 2, 8]
def baseStart_111506 : Nat := 118140960795 + 111506 * 2 ^ 59
def prefixEnd_111506 : Nat := 4983230072969 + 3 ^ 40 * 111506 * 2
def baseEnd_111506 : Nat := 1884976917213035916451

theorem tailTrace_111506 : CollatzResearch.WordTrace tailWord_111506 prefixEnd_111506 1884976917213035916451 := by
  unfold tailWord_111506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016739483510070138440593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2711305289360187035841581 1016739483510070138440593)
  ·
    refine ⟨762554612632552603830445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016739483510070138440593 762554612632552603830445)
    ·
      refine ⟨285957979737207226436417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 762554612632552603830445 285957979737207226436417)
      ·
        refine ⟨214468484802905419827313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285957979737207226436417 214468484802905419827313)
        ·
          refine ⟨160851363602179064870485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214468484802905419827313 160851363602179064870485)
          ·
            refine ⟨1884976917213035916451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 160851363602179064870485 1884976917213035916451)
            ·
              rfl

theorem cell20_111506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 8].length) (baseStart_111506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111506 prefixEnd_111506 := by exact prefixLift 111506
  have htrace : WordTrace (prefixWord ++ tailWord_111506) baseStart_111506 baseEnd_111506 := by
    simpa [prefixWord, tailWord_111506, baseEnd_111506] using wordTrace_append hprefix tailTrace_111506
  have hstable : (prefixWord ++ tailWord_111506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111506).length < 2 ^ (prefixWord ++ tailWord_111506).sum := by decide
  have hdescent : baseEnd_111506 < baseStart_111506 := by decide
  rcases family_descends (prefixWord ++ tailWord_111506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111537 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_111537 : Nat := 118140960795 + 111537 * 2 ^ 59
def prefixEnd_111537 : Nat := 4983230072969 + 3 ^ 40 * 111537 * 2
def baseEnd_111537 : Nat := 50908526009453639710717

theorem tailTrace_111537 : CollatzResearch.WordTrace tailWord_111537 prefixEnd_111537 50908526009453639710717 := by
  unfold tailWord_111537
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068088596927972848140865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2712059064618648565427243 4068088596927972848140865)
  ·
    refine ⟨3051066447695979636105649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4068088596927972848140865 3051066447695979636105649)
    ·
      refine ⟨2288299835771984727079237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3051066447695979636105649 2288299835771984727079237)
      ·
        refine ⟨429056219207247136327357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2288299835771984727079237 429056219207247136327357)
        ·
          refine ⟨160896082202717676122759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429056219207247136327357 160896082202717676122759)
          ·
            refine ⟨241344123304076514184139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160896082202717676122759 241344123304076514184139)
            ·
              refine ⟨362016184956114771276209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241344123304076514184139 362016184956114771276209)
              ·
                refine ⟨271512138717086078457157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362016184956114771276209 271512138717086078457157)
                ·
                  refine ⟨50908526009453639710717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271512138717086078457157 50908526009453639710717)
                  ·
                    rfl

theorem cell20_111537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_111537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111537 prefixEnd_111537 := by exact prefixLift 111537
  have htrace : WordTrace (prefixWord ++ tailWord_111537) baseStart_111537 baseEnd_111537 := by
    simpa [prefixWord, tailWord_111537, baseEnd_111537] using wordTrace_append hprefix tailTrace_111537
  have hstable : (prefixWord ++ tailWord_111537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111537).length < 2 ^ (prefixWord ++ tailWord_111537).sum := by decide
  have hdescent : baseEnd_111537 < baseStart_111537 := by decide
  rcases family_descends (prefixWord ++ tailWord_111537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111540 : List Nat := [2, 5, 2, 1, 1, 2, 3, 4]
def baseStart_111540 : Nat := 118140960795 + 111540 * 2 ^ 59
def prefixEnd_111540 : Nat := 4983230072969 + 3 ^ 40 * 111540 * 2
def baseEnd_111540 : Nat := 16969965097066320870235

theorem tailTrace_111540 : CollatzResearch.WordTrace tailWord_111540 prefixEnd_111540 16969965097066320870235 := by
  unfold tailWord_111540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034099007958552180250037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2712132010611402907000049 2034099007958552180250037)
  ·
    refine ⟨190696781996114266898441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2034099007958552180250037 190696781996114266898441)
    ·
      refine ⟨143022586497085700173831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190696781996114266898441 143022586497085700173831)
      ·
        refine ⟨214533879745628550260747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143022586497085700173831 214533879745628550260747)
        ·
          refine ⟨321800819618442825391121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214533879745628550260747 321800819618442825391121)
          ·
            refine ⟨241350614713832119043341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321800819618442825391121 241350614713832119043341)
            ·
              refine ⟨90506480517687044641253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241350614713832119043341 90506480517687044641253)
              ·
                refine ⟨16969965097066320870235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90506480517687044641253 16969965097066320870235)
                ·
                  rfl

theorem cell20_111540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_111540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111540 prefixEnd_111540 := by exact prefixLift 111540
  have htrace : WordTrace (prefixWord ++ tailWord_111540) baseStart_111540 baseEnd_111540 := by
    simpa [prefixWord, tailWord_111540, baseEnd_111540] using wordTrace_append hprefix tailTrace_111540
  have hstable : (prefixWord ++ tailWord_111540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111540).length < 2 ^ (prefixWord ++ tailWord_111540).sum := by decide
  have hdescent : baseEnd_111540 < baseStart_111540 := by decide
  rcases family_descends (prefixWord ++ tailWord_111540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111544 : List Nat := [2, 1, 2, 1, 2, 5, 3, 4]
def baseStart_111544 : Nat := 118140960795 + 111544 * 2 ^ 59
def prefixEnd_111544 : Nat := 4983230072969 + 3 ^ 40 * 111544 * 2
def baseEnd_111544 : Nat := 16970573666730908825785

theorem tailTrace_111544 : CollatzResearch.WordTrace tailWord_111544 prefixEnd_111544 16970573666730908825785 := by
  unfold tailWord_111544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034171953951306521822843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2712229271935075362430457 2034171953951306521822843)
  ·
    refine ⟨3051257930926959782734265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2034171953951306521822843 3051257930926959782734265)
    ·
      refine ⟨2288443448195219837050699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3051257930926959782734265 2288443448195219837050699)
      ·
        refine ⟨3432665172292829755576049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288443448195219837050699 3432665172292829755576049)
        ·
          refine ⟨2574498879219622316682037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3432665172292829755576049 2574498879219622316682037)
          ·
            refine ⟨241359269926839592188941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2574498879219622316682037 241359269926839592188941)
            ·
              refine ⟨90509726222564847070853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241359269926839592188941 90509726222564847070853)
              ·
                refine ⟨16970573666730908825785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90509726222564847070853 16970573666730908825785)
                ·
                  rfl

theorem cell20_111544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_111544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111544 prefixEnd_111544 := by exact prefixLift 111544
  have htrace : WordTrace (prefixWord ++ tailWord_111544) baseStart_111544 baseEnd_111544 := by
    simpa [prefixWord, tailWord_111544, baseEnd_111544] using wordTrace_append hprefix tailTrace_111544
  have hstable : (prefixWord ++ tailWord_111544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111544).length < 2 ^ (prefixWord ++ tailWord_111544).sum := by decide
  have hdescent : baseEnd_111544 < baseStart_111544 := by decide
  rcases family_descends (prefixWord ++ tailWord_111544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111605 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 2]
def baseStart_111605 : Nat := 118140960795 + 111605 * 2 ^ 59
def prefixEnd_111605 : Nat := 4983230072969 + 3 ^ 40 * 111605 * 2
def baseEnd_111605 : Nat := 50939563062347625443773

theorem tailTrace_111605 : CollatzResearch.WordTrace tailWord_111605 prefixEnd_111605 50939563062347625443773 := by
  unfold tailWord_111605
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070568760681620461616269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2713712507121080307744179 4070568760681620461616269)
  ·
    refine ⟨1526463285255607673106101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4070568760681620461616269 1526463285255607673106101)
    ·
      refine ⟨143105932992713219353697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1526463285255607673106101 143105932992713219353697)
      ·
        refine ⟨107329449744534914515273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143105932992713219353697 107329449744534914515273)
        ·
          refine ⟨80497087308401185886455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107329449744534914515273 80497087308401185886455)
          ·
            refine ⟨120745630962601778829683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80497087308401185886455 120745630962601778829683)
            ·
              refine ⟨181118446443902668244525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120745630962601778829683 181118446443902668244525)
              ·
                refine ⟨67919417416463500591697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181118446443902668244525 67919417416463500591697)
                ·
                  refine ⟨50939563062347625443773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67919417416463500591697 50939563062347625443773)
                  ·
                    rfl

theorem cell20_111605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_111605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111605 prefixEnd_111605 := by exact prefixLift 111605
  have htrace : WordTrace (prefixWord ++ tailWord_111605) baseStart_111605 baseEnd_111605 := by
    simpa [prefixWord, tailWord_111605, baseEnd_111605] using wordTrace_append hprefix tailTrace_111605
  have hstable : (prefixWord ++ tailWord_111605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111605).length < 2 ^ (prefixWord ++ tailWord_111605).sum := by decide
  have hdescent : baseEnd_111605 < baseStart_111605 := by decide
  rcases family_descends (prefixWord ++ tailWord_111605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111644 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_111644 : Nat := 118140960795 + 111644 * 2 ^ 59
def prefixEnd_111644 : Nat := 4983230072969 + 3 ^ 40 * 111644 * 2
def baseEnd_111644 : Nat := 50957363725036823143613

theorem tailTrace_111644 : CollatzResearch.WordTrace tailWord_111644 prefixEnd_111644 50957363725036823143613 := by
  unfold tailWord_111644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035995603770165061142993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2714660805026886748190657 2035995603770165061142993)
  ·
    refine ⟨1526996702827623795857245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2035995603770165061142993 1526996702827623795857245)
    ·
      refine ⟨572623763560358923446467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1526996702827623795857245 572623763560358923446467)
      ·
        refine ⟨858935645340538385169701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572623763560358923446467 858935645340538385169701)
        ·
          refine ⟨161050433501350947219319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 858935645340538385169701 161050433501350947219319)
          ·
            refine ⟨241575650252026420828979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161050433501350947219319 241575650252026420828979)
            ·
              refine ⟨362363475378039631243469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241575650252026420828979 362363475378039631243469)
              ·
                refine ⟨135886303266764861716301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362363475378039631243469 135886303266764861716301)
                ·
                  refine ⟨50957363725036823143613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135886303266764861716301 50957363725036823143613)
                  ·
                    rfl

theorem cell20_111644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_111644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111644 prefixEnd_111644 := by exact prefixLift 111644
  have htrace : WordTrace (prefixWord ++ tailWord_111644) baseStart_111644 baseEnd_111644 := by
    simpa [prefixWord, tailWord_111644, baseEnd_111644] using wordTrace_append hprefix tailTrace_111644
  have hstable : (prefixWord ++ tailWord_111644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111644).length < 2 ^ (prefixWord ++ tailWord_111644).sum := by decide
  have hdescent : baseEnd_111644 < baseStart_111644 := by decide
  rcases family_descends (prefixWord ++ tailWord_111644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111724 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_111724 : Nat := 118140960795 + 111724 * 2 ^ 59
def prefixEnd_111724 : Nat := 4983230072969 + 3 ^ 40 * 111724 * 2
def baseEnd_111724 : Nat := 50993877904912100476619

theorem tailTrace_111724 : CollatzResearch.WordTrace tailWord_111724 prefixEnd_111724 50993877904912100476619 := by
  unfold tailWord_111724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037454523625251892599113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2716606031500335856798817 2037454523625251892599113)
  ·
    refine ⟨1528090892718938919449335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2037454523625251892599113 1528090892718938919449335)
    ·
      refine ⟨2292136339078408379174003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528090892718938919449335 2292136339078408379174003)
      ·
        refine ⟨3438204508617612568761005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292136339078408379174003 3438204508617612568761005)
        ·
          refine ⟨1289326690731604713285377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3438204508617612568761005 1289326690731604713285377)
          ·
            refine ⟨966995018048703534964033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289326690731604713285377 966995018048703534964033)
            ·
              refine ⟨725246263536527651223025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966995018048703534964033 725246263536527651223025)
              ·
                refine ⟨543934697652395738417269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725246263536527651223025 543934697652395738417269)
                ·
                  refine ⟨50993877904912100476619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543934697652395738417269 50993877904912100476619)
                  ·
                    rfl

theorem cell20_111724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_111724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111724 prefixEnd_111724 := by exact prefixLift 111724
  have htrace : WordTrace (prefixWord ++ tailWord_111724) baseStart_111724 baseEnd_111724 := by
    simpa [prefixWord, tailWord_111724, baseEnd_111724] using wordTrace_append hprefix tailTrace_111724
  have hstable : (prefixWord ++ tailWord_111724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111724).length < 2 ^ (prefixWord ++ tailWord_111724).sum := by decide
  have hdescent : baseEnd_111724 < baseStart_111724 := by decide
  rcases family_descends (prefixWord ++ tailWord_111724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111727 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 2]
def baseStart_111727 : Nat := 118140960795 + 111727 * 2 ^ 59
def prefixEnd_111727 : Nat := 4983230072969 + 3 ^ 40 * 111727 * 2
def baseEnd_111727 : Nat := 50995247186657423376607

theorem tailTrace_111727 : CollatzResearch.WordTrace tailWord_111727 prefixEnd_111727 50995247186657423376607 := by
  unfold tailWord_111727
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075018466239635297557435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2716678977493090198371623 4075018466239635297557435)
  ·
    refine ⟨6112527699359452946336153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4075018466239635297557435 6112527699359452946336153)
    ·
      refine ⟨4584395774519589709752115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6112527699359452946336153 4584395774519589709752115)
      ·
        refine ⟨6876593661779384564628173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584395774519589709752115 6876593661779384564628173)
        ·
          refine ⟨2578722623167269211735565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6876593661779384564628173 2578722623167269211735565)
          ·
            refine ⟨967020983687725954400837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2578722623167269211735565 967020983687725954400837)
            ·
              refine ⟨181316434441448616450157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 967020983687725954400837 181316434441448616450157)
              ·
                refine ⟨67993662915543231168809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181316434441448616450157 67993662915543231168809)
                ·
                  refine ⟨50995247186657423376607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67993662915543231168809 50995247186657423376607)
                  ·
                    rfl

theorem cell20_111727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 2].length) (baseStart_111727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111727 prefixEnd_111727 := by exact prefixLift 111727
  have htrace : WordTrace (prefixWord ++ tailWord_111727) baseStart_111727 baseEnd_111727 := by
    simpa [prefixWord, tailWord_111727, baseEnd_111727] using wordTrace_append hprefix tailTrace_111727
  have hstable : (prefixWord ++ tailWord_111727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111727).length < 2 ^ (prefixWord ++ tailWord_111727).sum := by decide
  have hdescent : baseEnd_111727 < baseStart_111727 := by decide
  rcases family_descends (prefixWord ++ tailWord_111727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111737 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 3]
def baseStart_111737 : Nat := 118140960795 + 111737 * 2 ^ 59
def prefixEnd_111737 : Nat := 4983230072969 + 3 ^ 40 * 111737 * 2
def baseEnd_111737 : Nat := 50999811459141833043233

theorem tailTrace_111737 : CollatzResearch.WordTrace tailWord_111737 prefixEnd_111737 50999811459141833043233 := by
  unfold tailWord_111737
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075383196203407005421465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2716922130802271336947643 4075383196203407005421465)
  ·
    refine ⟨3056537397152555254066099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4075383196203407005421465 3056537397152555254066099)
    ·
      refine ⟨4584806095728832881099149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056537397152555254066099 4584806095728832881099149)
      ·
        refine ⟨1719302285898312330412181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4584806095728832881099149 1719302285898312330412181)
        ·
          refine ⟨80592294651483390488071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1719302285898312330412181 80592294651483390488071)
          ·
            refine ⟨120888441977225085732107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80592294651483390488071 120888441977225085732107)
            ·
              refine ⟨181332662965837628598161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120888441977225085732107 181332662965837628598161)
              ·
                refine ⟨135999497224378221448621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181332662965837628598161 135999497224378221448621)
                ·
                  refine ⟨50999811459141833043233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135999497224378221448621 50999811459141833043233)
                  ·
                    rfl

theorem cell20_111737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_111737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111737 prefixEnd_111737 := by exact prefixLift 111737
  have htrace : WordTrace (prefixWord ++ tailWord_111737) baseStart_111737 baseEnd_111737 := by
    simpa [prefixWord, tailWord_111737, baseEnd_111737] using wordTrace_append hprefix tailTrace_111737
  have hstable : (prefixWord ++ tailWord_111737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111737).length < 2 ^ (prefixWord ++ tailWord_111737).sum := by decide
  have hdescent : baseEnd_111737 < baseStart_111737 := by decide
  rcases family_descends (prefixWord ++ tailWord_111737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111748 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_111748 : Nat := 118140960795 + 111748 * 2 ^ 59
def prefixEnd_111748 : Nat := 4983230072969 + 3 ^ 40 * 111748 * 2
def baseEnd_111748 : Nat := 51004832158874683676521

theorem tailTrace_111748 : CollatzResearch.WordTrace tailWord_111748 prefixEnd_111748 51004832158874683676521 := by
  unfold tailWord_111748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037892199581777942035949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2717189599442370589381265 2037892199581777942035949)
  ·
    refine ⟨764209574843166728263481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2037892199581777942035949 764209574843166728263481)
    ·
      refine ⟨573157181132375046197611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 764209574843166728263481 573157181132375046197611)
      ·
        refine ⟨859735771698562569296417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573157181132375046197611 859735771698562569296417)
        ·
          refine ⟨644801828773921926972313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859735771698562569296417 644801828773921926972313)
          ·
            refine ⟨483601371580441445229235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644801828773921926972313 483601371580441445229235)
            ·
              refine ⟨725402057370662167843853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483601371580441445229235 725402057370662167843853)
              ·
                refine ⟨272025771513998312941445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725402057370662167843853 272025771513998312941445)
                ·
                  refine ⟨51004832158874683676521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272025771513998312941445 51004832158874683676521)
                  ·
                    rfl

theorem cell20_111748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_111748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111748 prefixEnd_111748 := by exact prefixLift 111748
  have htrace : WordTrace (prefixWord ++ tailWord_111748) baseStart_111748 baseEnd_111748 := by
    simpa [prefixWord, tailWord_111748, baseEnd_111748] using wordTrace_append hprefix tailTrace_111748
  have hstable : (prefixWord ++ tailWord_111748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111748).length < 2 ^ (prefixWord ++ tailWord_111748).sum := by decide
  have hdescent : baseEnd_111748 < baseStart_111748 := by decide
  rcases family_descends (prefixWord ++ tailWord_111748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111772 : List Nat := [2, 2, 3, 2, 1, 2, 4, 4]
def baseStart_111772 : Nat := 118140960795 + 111772 * 2 ^ 59
def prefixEnd_111772 : Nat := 4983230072969 + 3 ^ 40 * 111772 * 2
def baseEnd_111772 : Nat := 17005262137612422292141

theorem tailTrace_111772 : CollatzResearch.WordTrace tailWord_111772 prefixEnd_111772 17005262137612422292141 := by
  unfold tailWord_111772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038329875538303991472785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2717773167384405321963713 2038329875538303991472785)
  ·
    refine ⟨1528747406653727993604589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2038329875538303991472785 1528747406653727993604589)
    ·
      refine ⟨573280277495147997601721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1528747406653727993604589 573280277495147997601721)
      ·
        refine ⟨429960208121360998201291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573280277495147997601721 429960208121360998201291)
        ·
          refine ⟨644940312182041497301937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429960208121360998201291 644940312182041497301937)
          ·
            refine ⟨483705234136531122976453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644940312182041497301937 483705234136531122976453)
            ·
              refine ⟨90694731400599585558085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 483705234136531122976453 90694731400599585558085)
              ·
                refine ⟨17005262137612422292141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90694731400599585558085 17005262137612422292141)
                ·
                  rfl

theorem cell20_111772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_111772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111772 prefixEnd_111772 := by exact prefixLift 111772
  have htrace : WordTrace (prefixWord ++ tailWord_111772) baseStart_111772 baseEnd_111772 := by
    simpa [prefixWord, tailWord_111772, baseEnd_111772] using wordTrace_append hprefix tailTrace_111772
  have hstable : (prefixWord ++ tailWord_111772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111772).length < 2 ^ (prefixWord ++ tailWord_111772).sum := by decide
  have hdescent : baseEnd_111772 < baseStart_111772 := by decide
  rcases family_descends (prefixWord ++ tailWord_111772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111778 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_111778 : Nat := 118140960795 + 111778 * 2 ^ 59
def prefixEnd_111778 : Nat := 4983230072969 + 3 ^ 40 * 111778 * 2
def baseEnd_111778 : Nat := 51018524976327912676399

theorem tailTrace_111778 : CollatzResearch.WordTrace tailWord_111778 prefixEnd_111778 51018524976327912676399 := by
  unfold tailWord_111778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019219647263717751915997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2717919059369914005109325 1019219647263717751915997)
  ·
    refine ⟨382207367723894156968499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1019219647263717751915997 382207367723894156968499)
    ·
      refine ⟨573311051585841235452749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382207367723894156968499 573311051585841235452749)
      ·
        refine ⟨214991644344690463294781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573311051585841235452749 214991644344690463294781)
        ·
          refine ⟨80621866629258923735543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214991644344690463294781 80621866629258923735543)
          ·
            refine ⟨120932799943888385603315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80621866629258923735543 120932799943888385603315)
            ·
              refine ⟨181399199915832578404973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120932799943888385603315 181399199915832578404973)
              ·
                refine ⟨68024699968437216901865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181399199915832578404973 68024699968437216901865)
                ·
                  refine ⟨51018524976327912676399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68024699968437216901865 51018524976327912676399)
                  ·
                    rfl

theorem cell20_111778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_111778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111778 prefixEnd_111778 := by exact prefixLift 111778
  have htrace : WordTrace (prefixWord ++ tailWord_111778) baseStart_111778 baseEnd_111778 := by
    simpa [prefixWord, tailWord_111778, baseEnd_111778] using wordTrace_append hprefix tailTrace_111778
  have hstable : (prefixWord ++ tailWord_111778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111778).length < 2 ^ (prefixWord ++ tailWord_111778).sum := by decide
  have hdescent : baseEnd_111778 < baseStart_111778 := by decide
  rcases family_descends (prefixWord ++ tailWord_111778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111789 : List Nat := [1, 5, 2, 1, 4, 1, 6]
def baseStart_111789 : Nat := 118140960795 + 111789 * 2 ^ 59
def prefixEnd_111789 : Nat := 4983230072969 + 3 ^ 40 * 111789 * 2
def baseEnd_111789 : Nat := 5669282852895640367743

theorem tailTrace_111789 : CollatzResearch.WordTrace tailWord_111789 prefixEnd_111789 5669282852895640367743 := by
  unfold tailWord_111789
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077279792015019886314421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2718186528010013257542947 4077279792015019886314421)
  ·
    refine ⟨382244980501408114341977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4077279792015019886314421 382244980501408114341977)
    ·
      refine ⟨286683735376056085756483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382244980501408114341977 286683735376056085756483)
      ·
        refine ⟨430025603064084128634725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286683735376056085756483 430025603064084128634725)
        ·
          refine ⟨80629800574515774119011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430025603064084128634725 80629800574515774119011)
          ·
            refine ⟨120944700861773661178517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80629800574515774119011 120944700861773661178517)
            ·
              refine ⟨5669282852895640367743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120944700861773661178517 5669282852895640367743)
              ·
                rfl

theorem cell20_111789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 6].length) (baseStart_111789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111789 prefixEnd_111789 := by exact prefixLift 111789
  have htrace : WordTrace (prefixWord ++ tailWord_111789) baseStart_111789 baseEnd_111789 := by
    simpa [prefixWord, tailWord_111789, baseEnd_111789] using wordTrace_append hprefix tailTrace_111789
  have hstable : (prefixWord ++ tailWord_111789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111789).length < 2 ^ (prefixWord ++ tailWord_111789).sum := by decide
  have hdescent : baseEnd_111789 < baseStart_111789 := by decide
  rcases family_descends (prefixWord ++ tailWord_111789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111793 : List Nat := [1, 2, 2, 5, 1, 1, 8]
def baseStart_111793 : Nat := 118140960795 + 111793 * 2 ^ 59
def prefixEnd_111793 : Nat := 4983230072969 + 3 ^ 40 * 111793 * 2
def baseEnd_111793 : Nat := 5669485709450503019593

theorem tailTrace_111793 : CollatzResearch.WordTrace tailWord_111793 prefixEnd_111793 5669485709450503019593 := by
  unfold tailWord_111793
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077425684000528569460033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2718283789333685712973355 4077425684000528569460033)
  ·
    refine ⟨3058069263000396427095025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4077425684000528569460033 3058069263000396427095025)
    ·
      refine ⟨2293551947250297320321269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3058069263000396427095025 2293551947250297320321269)
      ·
        refine ⟨215020495054715373780119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2293551947250297320321269 215020495054715373780119)
        ·
          refine ⟨322530742582073060670179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215020495054715373780119 322530742582073060670179)
          ·
            refine ⟨483796113873109591005269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322530742582073060670179 483796113873109591005269)
            ·
              refine ⟨5669485709450503019593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 483796113873109591005269 5669485709450503019593)
              ·
                rfl

theorem cell20_111793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_111793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111793 prefixEnd_111793 := by exact prefixLift 111793
  have htrace : WordTrace (prefixWord ++ tailWord_111793) baseStart_111793 baseEnd_111793 := by
    simpa [prefixWord, tailWord_111793, baseEnd_111793] using wordTrace_append hprefix tailTrace_111793
  have hstable : (prefixWord ++ tailWord_111793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111793).length < 2 ^ (prefixWord ++ tailWord_111793).sum := by decide
  have hdescent : baseEnd_111793 < baseStart_111793 := by decide
  rcases family_descends (prefixWord ++ tailWord_111793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111852 : List Nat := [2, 2, 1, 1, 2, 12]
def baseStart_111852 : Nat := 118140960795 + 111852 * 2 ^ 59
def prefixEnd_111852 : Nat := 4983230072969 + 3 ^ 40 * 111852 * 2
def baseEnd_111852 : Nat := 1890825947878242378127

theorem tailTrace_111852 : CollatzResearch.WordTrace tailWord_111852 prefixEnd_111852 1890825947878242378127 := by
  unfold tailWord_111852
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039788795393390822928905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2719718393857854430571873 2039788795393390822928905)
  ·
    refine ⟨1529841596545043117196679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2039788795393390822928905 1529841596545043117196679)
    ·
      refine ⟨2294762394817564675795019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529841596545043117196679 2294762394817564675795019)
      ·
        refine ⟨3442143592226347013692529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294762394817564675795019 3442143592226347013692529)
        ·
          refine ⟨2581607694169760260269397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442143592226347013692529 2581607694169760260269397)
          ·
            refine ⟨1890825947878242378127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2581607694169760260269397 1890825947878242378127)
            ·
              rfl

theorem cell20_111852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 12].length) (baseStart_111852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111852 prefixEnd_111852 := by exact prefixLift 111852
  have htrace : WordTrace (prefixWord ++ tailWord_111852) baseStart_111852 baseEnd_111852 := by
    simpa [prefixWord, tailWord_111852, baseEnd_111852] using wordTrace_append hprefix tailTrace_111852
  have hstable : (prefixWord ++ tailWord_111852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111852).length < 2 ^ (prefixWord ++ tailWord_111852).sum := by decide
  have hdescent : baseEnd_111852 < baseStart_111852 := by decide
  rcases family_descends (prefixWord ++ tailWord_111852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111858 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_111858 : Nat := 118140960795 + 111858 * 2 ^ 59
def prefixEnd_111858 : Nat := 4983230072969 + 3 ^ 40 * 111858 * 2
def baseEnd_111858 : Nat := 51055039156203190009405

theorem tailTrace_111858 : CollatzResearch.WordTrace tailWord_111858 prefixEnd_111858 51055039156203190009405 := by
  unfold tailWord_111858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019949107191261167644057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2719864285843363113717485 1019949107191261167644057)
  ·
    refine ⟨764961830393445875733043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1019949107191261167644057 764961830393445875733043)
    ·
      refine ⟨1147442745590168813599565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764961830393445875733043 1147442745590168813599565)
      ·
        refine ⟨430291029596313305099837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1147442745590168813599565 430291029596313305099837)
        ·
          refine ⟨161359136098617489412439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430291029596313305099837 161359136098617489412439)
          ·
            refine ⟨242038704147926234118659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161359136098617489412439 242038704147926234118659)
            ·
              refine ⟨363058056221889351177989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242038704147926234118659 363058056221889351177989)
              ·
                refine ⟨68073385541604253345873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363058056221889351177989 68073385541604253345873)
                ·
                  refine ⟨51055039156203190009405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68073385541604253345873 51055039156203190009405)
                  ·
                    rfl

theorem cell20_111858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_111858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111858 prefixEnd_111858 := by exact prefixLift 111858
  have htrace : WordTrace (prefixWord ++ tailWord_111858) baseStart_111858 baseEnd_111858 := by
    simpa [prefixWord, tailWord_111858, baseEnd_111858] using wordTrace_append hprefix tailTrace_111858
  have hstable : (prefixWord ++ tailWord_111858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111858).length < 2 ^ (prefixWord ++ tailWord_111858).sum := by decide
  have hdescent : baseEnd_111858 < baseStart_111858 := by decide
  rcases family_descends (prefixWord ++ tailWord_111858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111862 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_111862 : Nat := 118140960795 + 111862 * 2 ^ 59
def prefixEnd_111862 : Nat := 4983230072969 + 3 ^ 40 * 111862 * 2
def baseEnd_111862 : Nat := 51056864865196953876055

theorem tailTrace_111862 : CollatzResearch.WordTrace tailWord_111862 prefixEnd_111862 51056864865196953876055 := by
  unfold tailWord_111862
  simp only [CollatzResearch.WordTrace]
  refine ⟨254996395046909584607615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2719961547167035569147893 254996395046909584607615)
  ·
    refine ⟨382494592570364376911423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254996395046909584607615 382494592570364376911423)
    ·
      refine ⟨573741888855546565367135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382494592570364376911423 573741888855546565367135)
      ·
        refine ⟨860612833283319848050703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573741888855546565367135 860612833283319848050703)
        ·
          refine ⟨1290919249924979772076055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860612833283319848050703 1290919249924979772076055)
          ·
            refine ⟨1936378874887469658114083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290919249924979772076055 1936378874887469658114083)
            ·
              refine ⟨2904568312331204487171125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936378874887469658114083 2904568312331204487171125)
              ·
                refine ⟨272303279281050420672293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2904568312331204487171125 272303279281050420672293)
                ·
                  refine ⟨51056864865196953876055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272303279281050420672293 51056864865196953876055)
                  ·
                    rfl

theorem cell20_111862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_111862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111862 prefixEnd_111862 := by exact prefixLift 111862
  have htrace : WordTrace (prefixWord ++ tailWord_111862) baseStart_111862 baseEnd_111862 := by
    simpa [prefixWord, tailWord_111862, baseEnd_111862] using wordTrace_append hprefix tailTrace_111862
  have hstable : (prefixWord ++ tailWord_111862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111862).length < 2 ^ (prefixWord ++ tailWord_111862).sum := by decide
  have hdescent : baseEnd_111862 < baseStart_111862 := by decide
  rcases family_descends (prefixWord ++ tailWord_111862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111883 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_111883 : Nat := 118140960795 + 111883 * 2 ^ 59
def prefixEnd_111883 : Nat := 4983230072969 + 3 ^ 40 * 111883 * 2
def baseEnd_111883 : Nat := 51066449837414214175969

theorem tailTrace_111883 : CollatzResearch.WordTrace tailWord_111883 prefixEnd_111883 51066449837414214175969 := by
  unfold tailWord_111883
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080708253674473940236303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2720472169116315960157535 4080708253674473940236303)
  ·
    refine ⟨6121062380511710910354455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4080708253674473940236303 6121062380511710910354455)
    ·
      refine ⟨9181593570767566365531683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6121062380511710910354455 9181593570767566365531683)
      ·
        refine ⟨13772390356151349548297525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9181593570767566365531683 13772390356151349548297525)
        ·
          refine ⟨1291161595889189020152893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13772390356151349548297525 1291161595889189020152893)
          ·
            refine ⟨484185598458445882557335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1291161595889189020152893 484185598458445882557335)
            ·
              refine ⟨726278397687668823836003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484185598458445882557335 726278397687668823836003)
              ·
                refine ⟨1089417596531503235754005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726278397687668823836003 1089417596531503235754005)
                ·
                  refine ⟨51066449837414214175969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1089417596531503235754005 51066449837414214175969)
                  ·
                    rfl

theorem cell20_111883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_111883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111883 prefixEnd_111883 := by exact prefixLift 111883
  have htrace : WordTrace (prefixWord ++ tailWord_111883) baseStart_111883 baseEnd_111883 := by
    simpa [prefixWord, tailWord_111883, baseEnd_111883] using wordTrace_append hprefix tailTrace_111883
  have hstable : (prefixWord ++ tailWord_111883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111883).length < 2 ^ (prefixWord ++ tailWord_111883).sum := by decide
  have hdescent : baseEnd_111883 < baseStart_111883 := by decide
  rcases family_descends (prefixWord ++ tailWord_111883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111886 : List Nat := [4, 1, 1, 2, 1, 4, 3, 4]
def baseStart_111886 : Nat := 118140960795 + 111886 * 2 ^ 59
def prefixEnd_111886 : Nat := 4983230072969 + 3 ^ 40 * 111886 * 2
def baseEnd_111886 : Nat := 17022606373053179025319

theorem tailTrace_111886 : CollatzResearch.WordTrace tailWord_111886 prefixEnd_111886 17022606373053179025319 := by
  unfold tailWord_111886
  simp only [CollatzResearch.WordTrace]
  refine ⟨510102209082950681574439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2720545115109070301730341 510102209082950681574439)
  ·
    refine ⟨765153313624426022361659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 510102209082950681574439 765153313624426022361659)
    ·
      refine ⟨1147729970436639033542489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765153313624426022361659 1147729970436639033542489)
      ·
        refine ⟨860797477827479275156867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1147729970436639033542489 860797477827479275156867)
        ·
          refine ⟨1291196216741218912735301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860797477827479275156867 1291196216741218912735301)
          ·
            refine ⟨242099290638978546137869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1291196216741218912735301 242099290638978546137869)
            ·
              refine ⟨90787233989616954801701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242099290638978546137869 90787233989616954801701)
              ·
                refine ⟨17022606373053179025319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90787233989616954801701 17022606373053179025319)
                ·
                  rfl

theorem cell20_111886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_111886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111886 prefixEnd_111886 := by exact prefixLift 111886
  have htrace : WordTrace (prefixWord ++ tailWord_111886) baseStart_111886 baseEnd_111886 := by
    simpa [prefixWord, tailWord_111886, baseEnd_111886] using wordTrace_append hprefix tailTrace_111886
  have hstable : (prefixWord ++ tailWord_111886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111886).length < 2 ^ (prefixWord ++ tailWord_111886).sum := by decide
  have hdescent : baseEnd_111886 < baseStart_111886 := by decide
  rcases family_descends (prefixWord ++ tailWord_111886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111917 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_111917 : Nat := 118140960795 + 111917 * 2 ^ 59
def prefixEnd_111917 : Nat := 4983230072969 + 3 ^ 40 * 111917 * 2
def baseEnd_111917 : Nat := 51081968363861207042497

theorem tailTrace_111917 : CollatzResearch.WordTrace tailWord_111917 prefixEnd_111917 51081968363861207042497 := by
  unfold tailWord_111917
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081948335551297746974005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2721298890367531831316003 4081948335551297746974005)
  ·
    refine ⟨382682656457934163778813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4081948335551297746974005 382682656457934163778813)
    ·
      refine ⟨143505996171725311417055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382682656457934163778813 143505996171725311417055)
      ·
        refine ⟨215258994257587967125583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143505996171725311417055 215258994257587967125583)
        ·
          refine ⟨322888491386381950688375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215258994257587967125583 322888491386381950688375)
          ·
            refine ⟨484332737079572926032563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322888491386381950688375 484332737079572926032563)
            ·
              refine ⟨726499105619359389048845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484332737079572926032563 726499105619359389048845)
              ·
                refine ⟨272437164607259770893317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726499105619359389048845 272437164607259770893317)
                ·
                  refine ⟨51081968363861207042497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272437164607259770893317 51081968363861207042497)
                  ·
                    rfl

theorem cell20_111917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_111917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111917 prefixEnd_111917 := by exact prefixLift 111917
  have htrace : WordTrace (prefixWord ++ tailWord_111917) baseStart_111917 baseEnd_111917 := by
    simpa [prefixWord, tailWord_111917, baseEnd_111917] using wordTrace_append hprefix tailTrace_111917
  have hstable : (prefixWord ++ tailWord_111917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111917).length < 2 ^ (prefixWord ++ tailWord_111917).sum := by decide
  have hdescent : baseEnd_111917 < baseStart_111917 := by decide
  rcases family_descends (prefixWord ++ tailWord_111917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111928 : List Nat := [2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_111928 : Nat := 118140960795 + 111928 * 2 ^ 59
def prefixEnd_111928 : Nat := 4983230072969 + 3 ^ 40 * 111928 * 2
def baseEnd_111928 : Nat := 17028996354531352558595

theorem tailTrace_111928 : CollatzResearch.WordTrace tailWord_111928 prefixEnd_111928 17028996354531352558595 := by
  unfold tailWord_111928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041174769255723312812219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2721566359007631083749625 2041174769255723312812219)
  ·
    refine ⟨3061762153883584969218329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041174769255723312812219 3061762153883584969218329)
    ·
      refine ⟨2296321615412688726913747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3061762153883584969218329 2296321615412688726913747)
      ·
        refine ⟨3444482423119033090370621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296321615412688726913747 3444482423119033090370621)
        ·
          refine ⟨1291680908669637408888983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3444482423119033090370621 1291680908669637408888983)
          ·
            refine ⟨1937521363004456113333475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291680908669637408888983 1937521363004456113333475)
            ·
              refine ⟨2906282044506684170000213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937521363004456113333475 2906282044506684170000213)
              ·
                refine ⟨17028996354531352558595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2906282044506684170000213 17028996354531352558595)
                ·
                  rfl

theorem cell20_111928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_111928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111928 prefixEnd_111928 := by exact prefixLift 111928
  have htrace : WordTrace (prefixWord ++ tailWord_111928) baseStart_111928 baseEnd_111928 := by
    simpa [prefixWord, tailWord_111928, baseEnd_111928] using wordTrace_append hprefix tailTrace_111928
  have hstable : (prefixWord ++ tailWord_111928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111928).length < 2 ^ (prefixWord ++ tailWord_111928).sum := by decide
  have hdescent : baseEnd_111928 < baseStart_111928 := by decide
  rcases family_descends (prefixWord ++ tailWord_111928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111945 : List Nat := [1, 2, 1, 1, 2, 3, 6, 4]
def baseStart_111945 : Nat := 118140960795 + 111945 * 2 ^ 59
def prefixEnd_111945 : Nat := 4983230072969 + 3 ^ 40 * 111945 * 2
def baseEnd_111945 : Nat := 17031582775605851369683

theorem tailTrace_111945 : CollatzResearch.WordTrace tailWord_111945 prefixEnd_111945 17031582775605851369683 := by
  unfold tailWord_111945
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082969579449858528993289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2721979719633239019328859 4082969579449858528993289)
  ·
    refine ⟨3062227184587393896744967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4082969579449858528993289 3062227184587393896744967)
    ·
      refine ⟨4593340776881090845117451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062227184587393896744967 4593340776881090845117451)
      ·
        refine ⟨6890011165321636267676177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593340776881090845117451 6890011165321636267676177)
        ·
          refine ⟨5167508373991227200757133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6890011165321636267676177 5167508373991227200757133)
          ·
            refine ⟨1937815640246710200283925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5167508373991227200757133 1937815640246710200283925)
            ·
              refine ⟨90835108136564540638309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1937815640246710200283925 90835108136564540638309)
              ·
                refine ⟨17031582775605851369683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90835108136564540638309 17031582775605851369683)
                ·
                  rfl

theorem cell20_111945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_111945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111945 prefixEnd_111945 := by exact prefixLift 111945
  have htrace : WordTrace (prefixWord ++ tailWord_111945) baseStart_111945 baseEnd_111945 := by
    simpa [prefixWord, tailWord_111945, baseEnd_111945] using wordTrace_append hprefix tailTrace_111945
  have hstable : (prefixWord ++ tailWord_111945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111945).length < 2 ^ (prefixWord ++ tailWord_111945).sum := by decide
  have hdescent : baseEnd_111945 < baseStart_111945 := by decide
  rcases family_descends (prefixWord ++ tailWord_111945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111972 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 2]
def baseStart_111972 : Nat := 118140960795 + 111972 * 2 ^ 59
def prefixEnd_111972 : Nat := 4983230072969 + 3 ^ 40 * 111972 * 2
def baseEnd_111972 : Nat := 51107071862525460208939

theorem tailTrace_111972 : CollatzResearch.WordTrace tailWord_111972 prefixEnd_111972 51107071862525460208939 := by
  unfold tailWord_111972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041977175176021070113085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2722636233568028093484113 2041977175176021070113085)
  ·
    refine ⟨765741440691007901292407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2041977175176021070113085 765741440691007901292407)
    ·
      refine ⟨1148612161036511851938611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765741440691007901292407 1148612161036511851938611)
      ·
        refine ⟨1722918241554767777907917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148612161036511851938611 1722918241554767777907917)
        ·
          refine ⟨646094340583037916715469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1722918241554767777907917 646094340583037916715469)
          ·
            refine ⟨242285377718639218768301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 646094340583037916715469 242285377718639218768301)
            ·
              refine ⟨90857016644489707038113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242285377718639218768301 90857016644489707038113)
              ·
                refine ⟨68142762483367280278585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90857016644489707038113 68142762483367280278585)
                ·
                  refine ⟨51107071862525460208939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68142762483367280278585 51107071862525460208939)
                  ·
                    rfl

theorem cell20_111972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_111972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111972 prefixEnd_111972 := by exact prefixLift 111972
  have htrace : WordTrace (prefixWord ++ tailWord_111972) baseStart_111972 baseEnd_111972 := by
    simpa [prefixWord, tailWord_111972, baseEnd_111972] using wordTrace_append hprefix tailTrace_111972
  have hstable : (prefixWord ++ tailWord_111972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111972).length < 2 ^ (prefixWord ++ tailWord_111972).sum := by decide
  have hdescent : baseEnd_111972 < baseStart_111972 := by decide
  rcases family_descends (prefixWord ++ tailWord_111972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111982 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_111982 : Nat := 118140960795 + 111982 * 2 ^ 59
def prefixEnd_111982 : Nat := 4983230072969 + 3 ^ 40 * 111982 * 2
def baseEnd_111982 : Nat := 51111636135009869875565

theorem tailTrace_111982 : CollatzResearch.WordTrace tailWord_111982 prefixEnd_111982 51111636135009869875565 := by
  unfold tailWord_111982
  simp only [CollatzResearch.WordTrace]
  refine ⟨510539885039476731011275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2722879386877209232060133 510539885039476731011275)
  ·
    refine ⟨765809827559215096516913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 510539885039476731011275 765809827559215096516913)
    ·
      refine ⟨574357370669411322387685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 765809827559215096516913 574357370669411322387685)
      ·
        refine ⟨107692007000514622947691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 574357370669411322387685 107692007000514622947691)
        ·
          refine ⟨161538010500771934421537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107692007000514622947691 161538010500771934421537)
          ·
            refine ⟨121153507875578950816153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161538010500771934421537 121153507875578950816153)
            ·
              refine ⟨90865130906684213112115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121153507875578950816153 90865130906684213112115)
              ·
                refine ⟨136297696360026319668173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90865130906684213112115 136297696360026319668173)
                ·
                  refine ⟨51111636135009869875565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136297696360026319668173 51111636135009869875565)
                  ·
                    rfl

theorem cell20_111982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_111982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111982 prefixEnd_111982 := by exact prefixLift 111982
  have htrace : WordTrace (prefixWord ++ tailWord_111982) baseStart_111982 baseEnd_111982 := by
    simpa [prefixWord, tailWord_111982, baseEnd_111982] using wordTrace_append hprefix tailTrace_111982
  have hstable : (prefixWord ++ tailWord_111982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111982).length < 2 ^ (prefixWord ++ tailWord_111982).sum := by decide
  have hdescent : baseEnd_111982 < baseStart_111982 := by decide
  rcases family_descends (prefixWord ++ tailWord_111982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111997 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_111997 : Nat := 118140960795 + 111997 * 2 ^ 59
def prefixEnd_111997 : Nat := 4983230072969 + 3 ^ 40 * 111997 * 2
def baseEnd_111997 : Nat := 51118482543736484375503

theorem tailTrace_111997 : CollatzResearch.WordTrace tailWord_111997 prefixEnd_111997 51118482543736484375503 := by
  unfold tailWord_111997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084866175261471409886245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2723244116840980939924163 4084866175261471409886245)
  ·
    refine ⟨765912407861525889353671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4084866175261471409886245 765912407861525889353671)
    ·
      refine ⟨1148868611792288834030507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765912407861525889353671 1148868611792288834030507)
      ·
        refine ⟨1723302917688433251045761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148868611792288834030507 1723302917688433251045761)
        ·
          refine ⟨1292477188266324938284321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723302917688433251045761 1292477188266324938284321)
          ·
            refine ⟨969357891199743703713241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292477188266324938284321 969357891199743703713241)
            ·
              refine ⟨727018418399807777784931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969357891199743703713241 727018418399807777784931)
              ·
                refine ⟨1090527627599711666677397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727018418399807777784931 1090527627599711666677397)
                ·
                  refine ⟨51118482543736484375503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1090527627599711666677397 51118482543736484375503)
                  ·
                    rfl

theorem cell20_111997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_111997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_111997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_111997 prefixEnd_111997 := by exact prefixLift 111997
  have htrace : WordTrace (prefixWord ++ tailWord_111997) baseStart_111997 baseEnd_111997 := by
    simpa [prefixWord, tailWord_111997, baseEnd_111997] using wordTrace_append hprefix tailTrace_111997
  have hstable : (prefixWord ++ tailWord_111997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111997).length < 2 ^ (prefixWord ++ tailWord_111997).sum := by decide
  have hdescent : baseEnd_111997 < baseStart_111997 := by decide
  rcases family_descends (prefixWord ++ tailWord_111997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112024 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_112024 : Nat := 118140960795 + 112024 * 2 ^ 59
def prefixEnd_112024 : Nat := 4983230072969 + 3 ^ 40 * 112024 * 2
def baseEnd_112024 : Nat := 51130806079444390475393

theorem tailTrace_112024 : CollatzResearch.WordTrace tailWord_112024 prefixEnd_112024 51130806079444390475393 := by
  unfold tailWord_112024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042925473081827510559563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2723900630775770014079417 2042925473081827510559563)
  ·
    refine ⟨3064388209622741265839345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2042925473081827510559563 3064388209622741265839345)
    ·
      refine ⟨2298291157217055949379509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3064388209622741265839345 2298291157217055949379509)
      ·
        refine ⟨215464795989098995254329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2298291157217055949379509 215464795989098995254329)
        ·
          refine ⟨161598596991824246440747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215464795989098995254329 161598596991824246440747)
          ·
            refine ⟨242397895487736369661121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161598596991824246440747 242397895487736369661121)
            ·
              refine ⟨181798421615802277245841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242397895487736369661121 181798421615802277245841)
              ·
                refine ⟨136348816211851707934381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181798421615802277245841 136348816211851707934381)
                ·
                  refine ⟨51130806079444390475393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136348816211851707934381 51130806079444390475393)
                  ·
                    rfl

theorem cell20_112024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_112024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112024 prefixEnd_112024 := by exact prefixLift 112024
  have htrace : WordTrace (prefixWord ++ tailWord_112024) baseStart_112024 baseEnd_112024 := by
    simpa [prefixWord, tailWord_112024, baseEnd_112024] using wordTrace_append hprefix tailTrace_112024
  have hstable : (prefixWord ++ tailWord_112024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112024).length < 2 ^ (prefixWord ++ tailWord_112024).sum := by decide
  have hdescent : baseEnd_112024 < baseStart_112024 := by decide
  rcases family_descends (prefixWord ++ tailWord_112024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112031 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 2]
def baseStart_112031 : Nat := 118140960795 + 112031 * 2 ^ 59
def prefixEnd_112031 : Nat := 4983230072969 + 3 ^ 40 * 112031 * 2
def baseEnd_112031 : Nat := 51134001070183477242031

theorem tailTrace_112031 : CollatzResearch.WordTrace tailWord_112031 prefixEnd_112031 51134001070183477242031 := by
  unfold tailWord_112031
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086106257138295216623947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2724070838092196811082631 4086106257138295216623947)
  ·
    refine ⟨6129159385707442824935921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4086106257138295216623947 6129159385707442824935921)
    ·
      refine ⟨4596869539280582118701941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6129159385707442824935921 4596869539280582118701941)
      ·
        refine ⟨430956519307554573628307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4596869539280582118701941 430956519307554573628307)
        ·
          refine ⟨646434778961331860442461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430956519307554573628307 646434778961331860442461)
          ·
            refine ⟨242413042110499447665923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 646434778961331860442461 242413042110499447665923)
            ·
              refine ⟨363619563165749171498885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242413042110499447665923 363619563165749171498885)
              ·
                refine ⟨68178668093577969656041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363619563165749171498885 68178668093577969656041)
                ·
                  refine ⟨51134001070183477242031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68178668093577969656041 51134001070183477242031)
                  ·
                    rfl

theorem cell20_112031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 2].length) (baseStart_112031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112031 prefixEnd_112031 := by exact prefixLift 112031
  have htrace : WordTrace (prefixWord ++ tailWord_112031) baseStart_112031 baseEnd_112031 := by
    simpa [prefixWord, tailWord_112031, baseEnd_112031] using wordTrace_append hprefix tailTrace_112031
  have hstable : (prefixWord ++ tailWord_112031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112031).length < 2 ^ (prefixWord ++ tailWord_112031).sum := by decide
  have hdescent : baseEnd_112031 < baseStart_112031 := by decide
  rcases family_descends (prefixWord ++ tailWord_112031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112035 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_112035 : Nat := 118140960795 + 112035 * 2 ^ 59
def prefixEnd_112035 : Nat := 4983230072969 + 3 ^ 40 * 112035 * 2
def baseEnd_112035 : Nat := 51135826779177241108681

theorem tailTrace_112035 : CollatzResearch.WordTrace tailWord_112035 prefixEnd_112035 51135826779177241108681 := by
  unfold tailWord_112035
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086252149123803899769559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2724168099415869266513039 4086252149123803899769559)
  ·
    refine ⟨6129378223685705849654339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4086252149123803899769559 6129378223685705849654339)
    ·
      refine ⟨9194067335528558774481509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129378223685705849654339 9194067335528558774481509)
      ·
        refine ⟨1723887625411604770215283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9194067335528558774481509 1723887625411604770215283)
        ·
          refine ⟨2585831438117407155322925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723887625411604770215283 2585831438117407155322925)
          ·
            refine ⟨969686789294027683246097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2585831438117407155322925 969686789294027683246097)
            ·
              refine ⟨727265091970520762434573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969686789294027683246097 727265091970520762434573)
              ·
                refine ⟨272724409488945285912965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727265091970520762434573 272724409488945285912965)
                ·
                  refine ⟨51135826779177241108681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272724409488945285912965 51135826779177241108681)
                  ·
                    rfl

theorem cell20_112035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_112035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112035 prefixEnd_112035 := by exact prefixLift 112035
  have htrace : WordTrace (prefixWord ++ tailWord_112035) baseStart_112035 baseEnd_112035 := by
    simpa [prefixWord, tailWord_112035, baseEnd_112035] using wordTrace_append hprefix tailTrace_112035
  have hstable : (prefixWord ++ tailWord_112035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112035).length < 2 ^ (prefixWord ++ tailWord_112035).sum := by decide
  have hdescent : baseEnd_112035 < baseStart_112035 := by decide
  rcases family_descends (prefixWord ++ tailWord_112035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112086 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_112086 : Nat := 118140960795 + 112086 * 2 ^ 59
def prefixEnd_112086 : Nat := 4983230072969 + 3 ^ 40 * 112086 * 2
def baseEnd_112086 : Nat := 51159104568847730408473

theorem tailTrace_112086 : CollatzResearch.WordTrace tailWord_112086 prefixEnd_112086 51159104568847730408473 := by
  unfold tailWord_112086
  simp only [CollatzResearch.WordTrace]
  refine ⟨255507016996189975617257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2725408181292693073250741 255507016996189975617257)
  ·
    refine ⟨191630262747142481712943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255507016996189975617257 191630262747142481712943)
    ·
      refine ⟨287445394120713722569415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191630262747142481712943 287445394120713722569415)
      ·
        refine ⟨431168091181070583854123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287445394120713722569415 431168091181070583854123)
        ·
          refine ⟨646752136771605875781185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431168091181070583854123 646752136771605875781185)
          ·
            refine ⟨485064102578704406835889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646752136771605875781185 485064102578704406835889)
            ·
              refine ⟨363798076934028305126917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485064102578704406835889 363798076934028305126917)
              ·
                refine ⟨68212139425130307211297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363798076934028305126917 68212139425130307211297)
                ·
                  refine ⟨51159104568847730408473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68212139425130307211297 51159104568847730408473)
                  ·
                    rfl

theorem cell20_112086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_112086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112086 prefixEnd_112086 := by exact prefixLift 112086
  have htrace : WordTrace (prefixWord ++ tailWord_112086) baseStart_112086 baseEnd_112086 := by
    simpa [prefixWord, tailWord_112086, baseEnd_112086] using wordTrace_append hprefix tailTrace_112086
  have hstable : (prefixWord ++ tailWord_112086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112086).length < 2 ^ (prefixWord ++ tailWord_112086).sum := by decide
  have hdescent : baseEnd_112086 < baseStart_112086 := by decide
  rcases family_descends (prefixWord ++ tailWord_112086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112090 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_112090 : Nat := 118140960795 + 112090 * 2 ^ 59
def prefixEnd_112090 : Nat := 4983230072969 + 3 ^ 40 * 112090 * 2
def baseEnd_112090 : Nat := 51160930277841494275123

theorem tailTrace_112090 : CollatzResearch.WordTrace tailWord_112090 prefixEnd_112090 51160930277841494275123 := by
  unfold tailWord_112090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022064540981137073255431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2725505442616365528681149 1022064540981137073255431)
  ·
    refine ⟨1533096811471705609883147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022064540981137073255431 1533096811471705609883147)
    ·
      refine ⟨2299645217207558414824721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533096811471705609883147 2299645217207558414824721)
      ·
        refine ⟨1724733912905668811118541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2299645217207558414824721 1724733912905668811118541)
        ·
          refine ⟨646775217339625804169453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1724733912905668811118541 646775217339625804169453)
          ·
            refine ⟨242540706502359676563545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 646775217339625804169453 242540706502359676563545)
            ·
              refine ⟨181905529876769757422659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242540706502359676563545 181905529876769757422659)
              ·
                refine ⟨272858294815154636133989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181905529876769757422659 272858294815154636133989)
                ·
                  refine ⟨51160930277841494275123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272858294815154636133989 51160930277841494275123)
                  ·
                    rfl

theorem cell20_112090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_112090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112090 prefixEnd_112090 := by exact prefixLift 112090
  have htrace : WordTrace (prefixWord ++ tailWord_112090) baseStart_112090 baseEnd_112090 := by
    simpa [prefixWord, tailWord_112090, baseEnd_112090] using wordTrace_append hprefix tailTrace_112090
  have hstable : (prefixWord ++ tailWord_112090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112090).length < 2 ^ (prefixWord ++ tailWord_112090).sum := by decide
  have hdescent : baseEnd_112090 < baseStart_112090 := by decide
  rcases family_descends (prefixWord ++ tailWord_112090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112111 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_112111 : Nat := 118140960795 + 112111 * 2 ^ 59
def prefixEnd_112111 : Nat := 4983230072969 + 3 ^ 40 * 112111 * 2
def baseEnd_112111 : Nat := 51170515250058754575037

theorem tailTrace_112111 : CollatzResearch.WordTrace tailWord_112111 prefixEnd_112111 51170515250058754575037 := by
  unfold tailWord_112111
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089024096848468879536187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2726016064565645919690791 4089024096848468879536187)
  ·
    refine ⟨6133536145272703319304281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4089024096848468879536187 6133536145272703319304281)
    ·
      refine ⟨4600152108954527489478211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6133536145272703319304281 4600152108954527489478211)
      ·
        refine ⟨6900228163431791234217317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600152108954527489478211 6900228163431791234217317)
        ·
          refine ⟨1293792780643460856415747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6900228163431791234217317 1293792780643460856415747)
          ·
            refine ⟨1940689170965191284623621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293792780643460856415747 1940689170965191284623621)
            ·
              refine ⟨363879219555973365866929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1940689170965191284623621 363879219555973365866929)
              ·
                refine ⟨272909414666980024400197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363879219555973365866929 272909414666980024400197)
                ·
                  refine ⟨51170515250058754575037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272909414666980024400197 51170515250058754575037)
                  ·
                    rfl

theorem cell20_112111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_112111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112111 prefixEnd_112111 := by exact prefixLift 112111
  have htrace : WordTrace (prefixWord ++ tailWord_112111) baseStart_112111 baseEnd_112111 := by
    simpa [prefixWord, tailWord_112111, baseEnd_112111] using wordTrace_append hprefix tailTrace_112111
  have hstable : (prefixWord ++ tailWord_112111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112111).length < 2 ^ (prefixWord ++ tailWord_112111).sum := by decide
  have hdescent : baseEnd_112111 < baseStart_112111 := by decide
  rcases family_descends (prefixWord ++ tailWord_112111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112114 : List Nat := [3, 2, 1, 4, 1, 1, 4, 4]
def baseStart_112114 : Nat := 118140960795 + 112114 * 2 ^ 59
def prefixEnd_112114 : Nat := 4983230072969 + 3 ^ 40 * 112114 * 2
def baseEnd_112114 : Nat := 17057294843934692491675

theorem tailTrace_112114 : CollatzResearch.WordTrace tailWord_112114 prefixEnd_112114 17057294843934692491675 := by
  unfold tailWord_112114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022283378959400097973849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2726089010558400261263597 1022283378959400097973849)
  ·
    refine ⟨766712534219550073480387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1022283378959400097973849 766712534219550073480387)
    ·
      refine ⟨1150068801329325110220581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766712534219550073480387 1150068801329325110220581)
      ·
        refine ⟨215637900249248458166359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1150068801329325110220581 215637900249248458166359)
        ·
          refine ⟨323456850373872687249539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215637900249248458166359 323456850373872687249539)
          ·
            refine ⟨485185275560809030874309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323456850373872687249539 485185275560809030874309)
            ·
              refine ⟨90972239167651693288933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485185275560809030874309 90972239167651693288933)
              ·
                refine ⟨17057294843934692491675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90972239167651693288933 17057294843934692491675)
                ·
                  rfl

theorem cell20_112114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_112114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112114 prefixEnd_112114 := by exact prefixLift 112114
  have htrace : WordTrace (prefixWord ++ tailWord_112114) baseStart_112114 baseEnd_112114 := by
    simpa [prefixWord, tailWord_112114, baseEnd_112114] using wordTrace_append hprefix tailTrace_112114
  have hstable : (prefixWord ++ tailWord_112114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112114).length < 2 ^ (prefixWord ++ tailWord_112114).sum := by decide
  have hdescent : baseEnd_112114 < baseStart_112114 := by decide
  rcases family_descends (prefixWord ++ tailWord_112114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112135 : List Nat := [1, 1, 4, 3, 2, 3, 6]
def baseStart_112135 : Nat := 118140960795 + 112135 * 2 ^ 59
def prefixEnd_112135 : Nat := 4983230072969 + 3 ^ 40 * 112135 * 2
def baseEnd_112135 : Nat := 5686829944891259752771

theorem tailTrace_112135 : CollatzResearch.WordTrace tailWord_112135 prefixEnd_112135 5686829944891259752771 := by
  unfold tailWord_112135
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089899448761520978409859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2726599632507680652273239 4089899448761520978409859)
  ·
    refine ⟨6134849173142281467614789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4089899448761520978409859 6134849173142281467614789)
    ·
      refine ⟨1150284219964177775177773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6134849173142281467614789 1150284219964177775177773)
      ·
        refine ⟨431356582486566665691665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1150284219964177775177773 431356582486566665691665)
        ·
          refine ⟨323517436864924999268749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431356582486566665691665 323517436864924999268749)
          ·
            refine ⟨121319038824346874725781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323517436864924999268749 121319038824346874725781)
            ·
              refine ⟨5686829944891259752771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121319038824346874725781 5686829944891259752771)
              ·
                rfl

theorem cell20_112135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_112135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112135 prefixEnd_112135 := by exact prefixLift 112135
  have htrace : WordTrace (prefixWord ++ tailWord_112135) baseStart_112135 baseEnd_112135 := by
    simpa [prefixWord, tailWord_112135, baseEnd_112135] using wordTrace_append hprefix tailTrace_112135
  have hstable : (prefixWord ++ tailWord_112135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112135).length < 2 ^ (prefixWord ++ tailWord_112135).sum := by decide
  have hdescent : baseEnd_112135 < baseStart_112135 := by decide
  rcases family_descends (prefixWord ++ tailWord_112135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112141 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 4]
def baseStart_112141 : Nat := 118140960795 + 112141 * 2 ^ 59
def prefixEnd_112141 : Nat := 4983230072969 + 3 ^ 40 * 112141 * 2
def baseEnd_112141 : Nat := 51184208067511983574915

theorem tailTrace_112141 : CollatzResearch.WordTrace tailWord_112141 prefixEnd_112141 51184208067511983574915 := by
  unfold tailWord_112141
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090118286739784003128277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2726745524493189335418851 4090118286739784003128277)
  ·
    refine ⟨95862147345463687573319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4090118286739784003128277 95862147345463687573319)
    ·
      refine ⟨143793221018195531359979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95862147345463687573319 143793221018195531359979)
      ·
        refine ⟨215689831527293297039969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143793221018195531359979 215689831527293297039969)
        ·
          refine ⟨161767373645469972779977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215689831527293297039969 161767373645469972779977)
          ·
            refine ⟨121325530234102479584983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161767373645469972779977 121325530234102479584983)
            ·
              refine ⟨181988295351153719377475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121325530234102479584983 181988295351153719377475)
              ·
                refine ⟨272982443026730579066213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181988295351153719377475 272982443026730579066213)
                ·
                  refine ⟨51184208067511983574915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272982443026730579066213 51184208067511983574915)
                  ·
                    rfl

theorem cell20_112141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_112141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112141 prefixEnd_112141 := by exact prefixLift 112141
  have htrace : WordTrace (prefixWord ++ tailWord_112141) baseStart_112141 baseEnd_112141 := by
    simpa [prefixWord, tailWord_112141, baseEnd_112141] using wordTrace_append hprefix tailTrace_112141
  have hstable : (prefixWord ++ tailWord_112141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112141).length < 2 ^ (prefixWord ++ tailWord_112141).sum := by decide
  have hdescent : baseEnd_112141 < baseStart_112141 := by decide
  rcases family_descends (prefixWord ++ tailWord_112141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112145 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 2]
def baseStart_112145 : Nat := 118140960795 + 112145 * 2 ^ 59
def prefixEnd_112145 : Nat := 4983230072969 + 3 ^ 40 * 112145 * 2
def baseEnd_112145 : Nat := 51186033776505747441565

theorem tailTrace_112145 : CollatzResearch.WordTrace tailWord_112145 prefixEnd_112145 51186033776505747441565 := by
  unfold tailWord_112145
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090264178725292686273889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2726842785816861790849259 4090264178725292686273889)
  ·
    refine ⟨3067698134043969514705417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4090264178725292686273889 3067698134043969514705417)
    ·
      refine ⟨2300773600532977136029063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3067698134043969514705417 2300773600532977136029063)
      ·
        refine ⟨3451160400799465704043595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300773600532977136029063 3451160400799465704043595)
        ·
          refine ⟨5176740601199198556065393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451160400799465704043595 5176740601199198556065393)
          ·
            refine ⟨3882555450899398917049045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5176740601199198556065393 3882555450899398917049045)
            ·
              refine ⟨90997393380454662118337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3882555450899398917049045 90997393380454662118337)
              ·
                refine ⟨68248045035340996588753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90997393380454662118337 68248045035340996588753)
                ·
                  refine ⟨51186033776505747441565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68248045035340996588753 51186033776505747441565)
                  ·
                    rfl

theorem cell20_112145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_112145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112145 prefixEnd_112145 := by exact prefixLift 112145
  have htrace : WordTrace (prefixWord ++ tailWord_112145) baseStart_112145 baseEnd_112145 := by
    simpa [prefixWord, tailWord_112145, baseEnd_112145] using wordTrace_append hprefix tailTrace_112145
  have hstable : (prefixWord ++ tailWord_112145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112145).length < 2 ^ (prefixWord ++ tailWord_112145).sum := by decide
  have hdescent : baseEnd_112145 < baseStart_112145 := by decide
  rcases family_descends (prefixWord ++ tailWord_112145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112159 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 3]
def baseStart_112159 : Nat := 118140960795 + 112159 * 2 ^ 59
def prefixEnd_112159 : Nat := 4983230072969 + 3 ^ 40 * 112159 * 2
def baseEnd_112159 : Nat := 51192423757983920974841

theorem tailTrace_112159 : CollatzResearch.WordTrace tailWord_112159 prefixEnd_112159 51192423757983920974841 := by
  unfold tailWord_112159
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090774800674573077283531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2727183200449715384855687 4090774800674573077283531)
  ·
    refine ⟨6136162201011859615925297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4090774800674573077283531 6136162201011859615925297)
    ·
      refine ⟨4602121650758894711943973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6136162201011859615925297 4602121650758894711943973)
      ·
        refine ⟨862897809517292758489495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4602121650758894711943973 862897809517292758489495)
        ·
          refine ⟨1294346714275939137734243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862897809517292758489495 1294346714275939137734243)
          ·
            refine ⟨1941520071413908706601365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294346714275939137734243 1941520071413908706601365)
            ·
              refine ⟨91008753347526970621939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1941520071413908706601365 91008753347526970621939)
              ·
                refine ⟨136513130021290455932909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91008753347526970621939 136513130021290455932909)
                ·
                  refine ⟨51192423757983920974841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136513130021290455932909 51192423757983920974841)
                  ·
                    rfl

theorem cell20_112159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_112159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112159 prefixEnd_112159 := by exact prefixLift 112159
  have htrace : WordTrace (prefixWord ++ tailWord_112159) baseStart_112159 baseEnd_112159 := by
    simpa [prefixWord, tailWord_112159, baseEnd_112159] using wordTrace_append hprefix tailTrace_112159
  have hstable : (prefixWord ++ tailWord_112159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112159).length < 2 ^ (prefixWord ++ tailWord_112159).sum := by decide
  have hdescent : baseEnd_112159 < baseStart_112159 := by decide
  rcases family_descends (prefixWord ++ tailWord_112159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112201 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_112201 : Nat := 118140960795 + 112201 * 2 ^ 59
def prefixEnd_112201 : Nat := 4983230072969 + 3 ^ 40 * 112201 * 2
def baseEnd_112201 : Nat := 51211593702418441574669

theorem tailTrace_112201 : CollatzResearch.WordTrace tailWord_112201 prefixEnd_112201 51211593702418441574669 := by
  unfold tailWord_112201
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092306666522414250312457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2728204444348276166874971 4092306666522414250312457)
  ·
    refine ⟨3069229999891810687734343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4092306666522414250312457 3069229999891810687734343)
    ·
      refine ⟨4603844999837716031601515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069229999891810687734343 4603844999837716031601515)
      ·
        refine ⟨6905767499756574047402273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4603844999837716031601515 6905767499756574047402273)
        ·
          refine ⟨5179325624817430535551705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6905767499756574047402273 5179325624817430535551705)
          ·
            refine ⟨3884494218613072901663779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5179325624817430535551705 3884494218613072901663779)
            ·
              refine ⟨5826741327919609352495669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884494218613072901663779 5826741327919609352495669)
              ·
                refine ⟨546256999492463376796469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5826741327919609352495669 546256999492463376796469)
                ·
                  refine ⟨51211593702418441574669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546256999492463376796469 51211593702418441574669)
                  ·
                    rfl

theorem cell20_112201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_112201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112201 prefixEnd_112201 := by exact prefixLift 112201
  have htrace : WordTrace (prefixWord ++ tailWord_112201) baseStart_112201 baseEnd_112201 := by
    simpa [prefixWord, tailWord_112201, baseEnd_112201] using wordTrace_append hprefix tailTrace_112201
  have hstable : (prefixWord ++ tailWord_112201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112201).length < 2 ^ (prefixWord ++ tailWord_112201).sum := by decide
  have hdescent : baseEnd_112201 < baseStart_112201 := by decide
  rcases family_descends (prefixWord ++ tailWord_112201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112225 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_112225 : Nat := 118140960795 + 112225 * 2 ^ 59
def prefixEnd_112225 : Nat := 4983230072969 + 3 ^ 40 * 112225 * 2
def baseEnd_112225 : Nat := 51222547956381024774571

theorem tailTrace_112225 : CollatzResearch.WordTrace tailWord_112225 prefixEnd_112225 51222547956381024774571 := by
  unfold tailWord_112225
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093182018435466349186129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2728788012290310899457419 4093182018435466349186129)
  ·
    refine ⟨3069886513826599761889597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4093182018435466349186129 3069886513826599761889597)
    ·
      refine ⟨1151207442684974910708599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3069886513826599761889597 1151207442684974910708599)
      ·
        refine ⟨1726811164027462366062899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151207442684974910708599 1726811164027462366062899)
        ·
          refine ⟨2590216746041193549094349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726811164027462366062899 2590216746041193549094349)
          ·
            refine ⟨971331279765447580910381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2590216746041193549094349 971331279765447580910381)
            ·
              refine ⟨364249229912042842841393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971331279765447580910381 364249229912042842841393)
              ·
                refine ⟨273186922434032132131045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364249229912042842841393 273186922434032132131045)
                ·
                  refine ⟨51222547956381024774571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273186922434032132131045 51222547956381024774571)
                  ·
                    rfl

theorem cell20_112225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_112225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112225 prefixEnd_112225 := by exact prefixLift 112225
  have htrace : WordTrace (prefixWord ++ tailWord_112225) baseStart_112225 baseEnd_112225 := by
    simpa [prefixWord, tailWord_112225, baseEnd_112225] using wordTrace_append hprefix tailTrace_112225
  have hstable : (prefixWord ++ tailWord_112225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112225).length < 2 ^ (prefixWord ++ tailWord_112225).sum := by decide
  have hdescent : baseEnd_112225 < baseStart_112225 := by decide
  rcases family_descends (prefixWord ++ tailWord_112225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112238 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_112238 : Nat := 118140960795 + 112238 * 2 ^ 59
def prefixEnd_112238 : Nat := 4983230072969 + 3 ^ 40 * 112238 * 2
def baseEnd_112238 : Nat := 51228481510610757341185

theorem tailTrace_112238 : CollatzResearch.WordTrace tailWord_112238 prefixEnd_112238 51228481510610757341185 := by
  unfold tailWord_112238
  simp only [CollatzResearch.WordTrace]
  refine ⟨511707020923546196176171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2729104111592246379606245 511707020923546196176171)
  ·
    refine ⟨767560531385319294264257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511707020923546196176171 767560531385319294264257)
    ·
      refine ⟨575670398538989470698193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 767560531385319294264257 575670398538989470698193)
      ·
        refine ⟨431752798904242103023645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575670398538989470698193 431752798904242103023645)
        ·
          refine ⟨161907299589090788633867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431752798904242103023645 161907299589090788633867)
          ·
            refine ⟨242860949383636182950801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161907299589090788633867 242860949383636182950801)
            ·
              refine ⟨182145712037727137213101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242860949383636182950801 182145712037727137213101)
              ·
                refine ⟨68304642014147676454913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182145712037727137213101 68304642014147676454913)
                ·
                  refine ⟨51228481510610757341185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68304642014147676454913 51228481510610757341185)
                  ·
                    rfl

theorem cell20_112238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_112238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112238 prefixEnd_112238 := by exact prefixLift 112238
  have htrace : WordTrace (prefixWord ++ tailWord_112238) baseStart_112238 baseEnd_112238 := by
    simpa [prefixWord, tailWord_112238, baseEnd_112238] using wordTrace_append hprefix tailTrace_112238
  have hstable : (prefixWord ++ tailWord_112238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112238).length < 2 ^ (prefixWord ++ tailWord_112238).sum := by decide
  have hdescent : baseEnd_112238 < baseStart_112238 := by decide
  rcases family_descends (prefixWord ++ tailWord_112238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112239 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_112239 : Nat := 118140960795 + 112239 * 2 ^ 59
def prefixEnd_112239 : Nat := 4983230072969 + 3 ^ 40 * 112239 * 2
def baseEnd_112239 : Nat := 51228937937859198307847

theorem tailTrace_112239 : CollatzResearch.WordTrace tailWord_112239 prefixEnd_112239 51228937937859198307847 := by
  unfold tailWord_112239
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093692640384746740195771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2729128426923164493463847 4093692640384746740195771)
  ·
    refine ⟨6140538960577120110293657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4093692640384746740195771 6140538960577120110293657)
    ·
      refine ⟨4605404220432840082720243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6140538960577120110293657 4605404220432840082720243)
      ·
        refine ⟨6908106330649260124080365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605404220432840082720243 6908106330649260124080365)
        ·
          refine ⟨2590539873993472546530137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6908106330649260124080365 2590539873993472546530137)
          ·
            refine ⟨1942904905495104409897603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2590539873993472546530137 1942904905495104409897603)
            ·
              refine ⟨2914357358242656614846405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942904905495104409897603 2914357358242656614846405)
              ·
                refine ⟨546442004670498115283701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2914357358242656614846405 546442004670498115283701)
                ·
                  refine ⟨51228937937859198307847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546442004670498115283701 51228937937859198307847)
                  ·
                    rfl

theorem cell20_112239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_112239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112239 prefixEnd_112239 := by exact prefixLift 112239
  have htrace : WordTrace (prefixWord ++ tailWord_112239) baseStart_112239 baseEnd_112239 := by
    simpa [prefixWord, tailWord_112239, baseEnd_112239] using wordTrace_append hprefix tailTrace_112239
  have hstable : (prefixWord ++ tailWord_112239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112239).length < 2 ^ (prefixWord ++ tailWord_112239).sum := by decide
  have hdescent : baseEnd_112239 < baseStart_112239 := by decide
  rcases family_descends (prefixWord ++ tailWord_112239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112263 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_112263 : Nat := 118140960795 + 112263 * 2 ^ 59
def prefixEnd_112263 : Nat := 4983230072969 + 3 ^ 40 * 112263 * 2
def baseEnd_112263 : Nat := 51239892191821781507749

theorem tailTrace_112263 : CollatzResearch.WordTrace tailWord_112263 prefixEnd_112263 51239892191821781507749 := by
  unfold tailWord_112263
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094567992297798839069443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2729711994865199226046295 4094567992297798839069443)
  ·
    refine ⟨6141851988446698258604165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4094567992297798839069443 6141851988446698258604165)
    ·
      refine ⟨1151597247833755923488281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6141851988446698258604165 1151597247833755923488281)
      ·
        refine ⟨863697935875316942616211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151597247833755923488281 863697935875316942616211)
        ·
          refine ⟨1295546903812975413924317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863697935875316942616211 1295546903812975413924317)
          ·
            refine ⟨485830088929865780221619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1295546903812975413924317 485830088929865780221619)
            ·
              refine ⟨728745133394798670332429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485830088929865780221619 728745133394798670332429)
              ·
                refine ⟨273279425023049501374661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 728745133394798670332429 273279425023049501374661)
                ·
                  refine ⟨51239892191821781507749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273279425023049501374661 51239892191821781507749)
                  ·
                    rfl

theorem cell20_112263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_112263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112263 prefixEnd_112263 := by exact prefixLift 112263
  have htrace : WordTrace (prefixWord ++ tailWord_112263) baseStart_112263 baseEnd_112263 := by
    simpa [prefixWord, tailWord_112263, baseEnd_112263] using wordTrace_append hprefix tailTrace_112263
  have hstable : (prefixWord ++ tailWord_112263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112263).length < 2 ^ (prefixWord ++ tailWord_112263).sum := by decide
  have hdescent : baseEnd_112263 < baseStart_112263 := by decide
  rcases family_descends (prefixWord ++ tailWord_112263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112318 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_112318 : Nat := 118140960795 + 112318 * 2 ^ 59
def prefixEnd_112318 : Nat := 4983230072969 + 3 ^ 40 * 112318 * 2
def baseEnd_112318 : Nat := 51264995690486034674191

theorem tailTrace_112318 : CollatzResearch.WordTrace tailWord_112318 prefixEnd_112318 51264995690486034674191 := by
  unfold tailWord_112318
  simp only [CollatzResearch.WordTrace]
  refine ⟨512071750887317904040201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2731049338065695488214405 512071750887317904040201)
  ·
    refine ⟨384053813165488428030151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 512071750887317904040201 384053813165488428030151)
    ·
      refine ⟨576080719748232642045227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384053813165488428030151 576080719748232642045227)
      ·
        refine ⟨864121079622348963067841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576080719748232642045227 864121079622348963067841)
        ·
          refine ⟨648090809716761722300881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864121079622348963067841 648090809716761722300881)
          ·
            refine ⟨486068107287571291725661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648090809716761722300881 486068107287571291725661)
            ·
              refine ⟨182275540232839234397123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486068107287571291725661 182275540232839234397123)
              ·
                refine ⟨273413310349258851595685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182275540232839234397123 273413310349258851595685)
                ·
                  refine ⟨51264995690486034674191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273413310349258851595685 51264995690486034674191)
                  ·
                    rfl

theorem cell20_112318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_112318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112318 prefixEnd_112318 := by exact prefixLift 112318
  have htrace : WordTrace (prefixWord ++ tailWord_112318) baseStart_112318 baseEnd_112318 := by
    simpa [prefixWord, tailWord_112318, baseEnd_112318] using wordTrace_append hprefix tailTrace_112318
  have hstable : (prefixWord ++ tailWord_112318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112318).length < 2 ^ (prefixWord ++ tailWord_112318).sum := by decide
  have hdescent : baseEnd_112318 < baseStart_112318 := by decide
  rcases family_descends (prefixWord ++ tailWord_112318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112346 : List Nat := [3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_112346 : Nat := 118140960795 + 112346 * 2 ^ 59
def prefixEnd_112346 : Nat := 4983230072969 + 3 ^ 40 * 112346 * 2
def baseEnd_112346 : Nat := 17092591884480793913581

theorem tailTrace_112346 : CollatzResearch.WordTrace tailWord_112346 prefixEnd_112346 17092591884480793913581 := by
  unfold tailWord_112346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024398812749276003585223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2731730167331402676227261 1024398812749276003585223)
  ·
    refine ⟨1536598219123914005377835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1024398812749276003585223 1536598219123914005377835)
    ·
      refine ⟨2304897328685871008066753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1536598219123914005377835 2304897328685871008066753)
      ·
        refine ⟨1728672996514403256050065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2304897328685871008066753 1728672996514403256050065)
        ·
          refine ⟨1296504747385802442037549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1728672996514403256050065 1296504747385802442037549)
          ·
            refine ⟨486189280269675915764081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1296504747385802442037549 486189280269675915764081)
            ·
              refine ⟨364641960202256936823061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486189280269675915764081 364641960202256936823061)
              ·
                refine ⟨17092591884480793913581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 364641960202256936823061 17092591884480793913581)
                ·
                  rfl

theorem cell20_112346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_112346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112346 prefixEnd_112346 := by exact prefixLift 112346
  have htrace : WordTrace (prefixWord ++ tailWord_112346) baseStart_112346 baseEnd_112346 := by
    simpa [prefixWord, tailWord_112346, baseEnd_112346] using wordTrace_append hprefix tailTrace_112346
  have hstable : (prefixWord ++ tailWord_112346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112346).length < 2 ^ (prefixWord ++ tailWord_112346).sum := by decide
  have hdescent : baseEnd_112346 < baseStart_112346 := by decide
  rcases family_descends (prefixWord ++ tailWord_112346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112356 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 2]
def baseStart_112356 : Nat := 118140960795 + 112356 * 2 ^ 59
def prefixEnd_112356 : Nat := 4983230072969 + 3 ^ 40 * 112356 * 2
def baseEnd_112356 : Nat := 51282339925926791407369

theorem tailTrace_112356 : CollatzResearch.WordTrace tailWord_112356 prefixEnd_112356 51282339925926791407369 := by
  unfold tailWord_112356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2048979990480437861102461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2731973320640583814803281 2048979990480437861102461)
  ·
    refine ⟨768367496430164197913423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2048979990480437861102461 768367496430164197913423)
    ·
      refine ⟨1152551244645246296870135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768367496430164197913423 1152551244645246296870135)
      ·
        refine ⟨1728826866967869445305203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152551244645246296870135 1728826866967869445305203)
        ·
          refine ⟨2593240300451804167957805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728826866967869445305203 2593240300451804167957805)
          ·
            refine ⟨972465112669426562984177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2593240300451804167957805 972465112669426562984177)
            ·
              refine ⟨729348834502069922238133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972465112669426562984177 729348834502069922238133)
              ·
                refine ⟨68376453234569055209825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 729348834502069922238133 68376453234569055209825)
                ·
                  refine ⟨51282339925926791407369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68376453234569055209825 51282339925926791407369)
                  ·
                    rfl

theorem cell20_112356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_112356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112356 prefixEnd_112356 := by exact prefixLift 112356
  have htrace : WordTrace (prefixWord ++ tailWord_112356) baseStart_112356 baseEnd_112356 := by
    simpa [prefixWord, tailWord_112356, baseEnd_112356] using wordTrace_append hprefix tailTrace_112356
  have hstable : (prefixWord ++ tailWord_112356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112356).length < 2 ^ (prefixWord ++ tailWord_112356).sum := by decide
  have hdescent : baseEnd_112356 < baseStart_112356 := by decide
  rcases family_descends (prefixWord ++ tailWord_112356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112487 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 2]
def baseStart_112487 : Nat := 118140960795 + 112487 * 2 ^ 59
def prefixEnd_112487 : Nat := 4983230072969 + 3 ^ 40 * 112487 * 2
def baseEnd_112487 : Nat := 51342131895472558040167

theorem tailTrace_112487 : CollatzResearch.WordTrace tailWord_112487 prefixEnd_112487 51342131895472558040167 := by
  unfold tailWord_112487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102737943486285095223715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2735158628990856730149143 4102737943486285095223715)
  ·
    refine ⟨6154106915229427642835573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102737943486285095223715 6154106915229427642835573)
    ·
      refine ⟨576947523302758841515835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6154106915229427642835573 576947523302758841515835)
      ·
        refine ⟨865421284954138262273753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576947523302758841515835 865421284954138262273753)
        ·
          refine ⟨649065963715603696705315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865421284954138262273753 649065963715603696705315)
          ·
            refine ⟨973598945573405545057973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649065963715603696705315 973598945573405545057973)
            ·
              refine ⟨91274901147506769849185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 973598945573405545057973 91274901147506769849185)
              ·
                refine ⟨68456175860630077386889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91274901147506769849185 68456175860630077386889)
                ·
                  refine ⟨51342131895472558040167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68456175860630077386889 51342131895472558040167)
                  ·
                    rfl

theorem cell20_112487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 2].length) (baseStart_112487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112487 prefixEnd_112487 := by exact prefixLift 112487
  have htrace : WordTrace (prefixWord ++ tailWord_112487) baseStart_112487 baseEnd_112487 := by
    simpa [prefixWord, tailWord_112487, baseEnd_112487] using wordTrace_append hprefix tailTrace_112487
  have hstable : (prefixWord ++ tailWord_112487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112487).length < 2 ^ (prefixWord ++ tailWord_112487).sum := by decide
  have hdescent : baseEnd_112487 < baseStart_112487 := by decide
  rcases family_descends (prefixWord ++ tailWord_112487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112512 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_112512 : Nat := 118140960795 + 112512 * 2 ^ 59
def prefixEnd_112512 : Nat := 4983230072969 + 3 ^ 40 * 112512 * 2
def baseEnd_112512 : Nat := 51353542576683582206731

theorem tailTrace_112512 : CollatzResearch.WordTrace tailWord_112512 prefixEnd_112512 51353542576683582206731 := by
  unfold tailWord_112512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051824884197857182441895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2735766512263809576589193 2051824884197857182441895)
  ·
    refine ⟨3077737326296785773662843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2051824884197857182441895 3077737326296785773662843)
    ·
      refine ⟨4616605989445178660494265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077737326296785773662843 4616605989445178660494265)
      ·
        refine ⟨3462454492083883995370699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616605989445178660494265 3462454492083883995370699)
        ·
          refine ⟨5193681738125825993056049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462454492083883995370699 5193681738125825993056049)
          ·
            refine ⟨3895261303594369494792037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193681738125825993056049 3895261303594369494792037)
            ·
              refine ⟨730361494423944280273507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3895261303594369494792037 730361494423944280273507)
              ·
                refine ⟨1095542241635916420410261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730361494423944280273507 1095542241635916420410261)
                ·
                  refine ⟨51353542576683582206731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1095542241635916420410261 51353542576683582206731)
                  ·
                    rfl

theorem cell20_112512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_112512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112512 prefixEnd_112512 := by exact prefixLift 112512
  have htrace : WordTrace (prefixWord ++ tailWord_112512) baseStart_112512 baseEnd_112512 := by
    simpa [prefixWord, tailWord_112512, baseEnd_112512] using wordTrace_append hprefix tailTrace_112512
  have hstable : (prefixWord ++ tailWord_112512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112512).length < 2 ^ (prefixWord ++ tailWord_112512).sum := by decide
  have hdescent : baseEnd_112512 < baseStart_112512 := by decide
  rcases family_descends (prefixWord ++ tailWord_112512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112536 : List Nat := [2, 1, 2, 6, 9]
def baseStart_112536 : Nat := 118140960795 + 112536 * 2 ^ 59
def prefixEnd_112536 : Nat := 4983230072969 + 3 ^ 40 * 112536 * 2
def baseEnd_112536 : Nat := 634129590501804511193

theorem tailTrace_112536 : CollatzResearch.WordTrace tailWord_112536 prefixEnd_112536 634129590501804511193 := by
  unfold tailWord_112536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052262560154383231878731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2736350080205844309171641 2052262560154383231878731)
  ·
    refine ⟨3078393840231574847818097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2052262560154383231878731 3078393840231574847818097)
    ·
      refine ⟨2308795380173681135863573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3078393840231574847818097 2308795380173681135863573)
      ·
        refine ⟨108224783445641303243605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2308795380173681135863573 108224783445641303243605)
        ·
          refine ⟨634129590501804511193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 108224783445641303243605 634129590501804511193)
          ·
            rfl

theorem cell20_112536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 9].length) (baseStart_112536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112536 prefixEnd_112536 := by exact prefixLift 112536
  have htrace : WordTrace (prefixWord ++ tailWord_112536) baseStart_112536 baseEnd_112536 := by
    simpa [prefixWord, tailWord_112536, baseEnd_112536] using wordTrace_append hprefix tailTrace_112536
  have hstable : (prefixWord ++ tailWord_112536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112536).length < 2 ^ (prefixWord ++ tailWord_112536).sum := by decide
  have hdescent : baseEnd_112536 < baseStart_112536 := by decide
  rcases family_descends (prefixWord ++ tailWord_112536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112584 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 2]
def baseStart_112584 : Nat := 118140960795 + 112584 * 2 ^ 59
def prefixEnd_112584 : Nat := 4983230072969 + 3 ^ 40 * 112584 * 2
def baseEnd_112584 : Nat := 51386405338571331806437

theorem tailTrace_112584 : CollatzResearch.WordTrace tailWord_112584 prefixEnd_112584 51386405338571331806437 := by
  unfold tailWord_112584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053137912067435330752403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2737517216089913774336537 2053137912067435330752403)
  ·
    refine ⟨3079706868101152996128605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2053137912067435330752403 3079706868101152996128605)
    ·
      refine ⟨1154890075537932373548227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3079706868101152996128605 1154890075537932373548227)
      ·
        refine ⟨1732335113306898560322341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154890075537932373548227 1732335113306898560322341)
        ·
          refine ⟨324812833745043480060439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1732335113306898560322341 324812833745043480060439)
          ·
            refine ⟨487219250617565220090659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324812833745043480060439 487219250617565220090659)
            ·
              refine ⟨730828875926347830135989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487219250617565220090659 730828875926347830135989)
              ·
                refine ⟨68515207118095109075249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730828875926347830135989 68515207118095109075249)
                ·
                  refine ⟨51386405338571331806437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68515207118095109075249 51386405338571331806437)
                  ·
                    rfl

theorem cell20_112584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_112584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112584 prefixEnd_112584 := by exact prefixLift 112584
  have htrace : WordTrace (prefixWord ++ tailWord_112584) baseStart_112584 baseEnd_112584 := by
    simpa [prefixWord, tailWord_112584, baseEnd_112584] using wordTrace_append hprefix tailTrace_112584
  have hstable : (prefixWord ++ tailWord_112584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112584).length < 2 ^ (prefixWord ++ tailWord_112584).sum := by decide
  have hdescent : baseEnd_112584 < baseStart_112584 := by decide
  rcases family_descends (prefixWord ++ tailWord_112584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112594 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_112594 : Nat := 118140960795 + 112594 * 2 ^ 59
def prefixEnd_112594 : Nat := 4983230072969 + 3 ^ 40 * 112594 * 2
def baseEnd_112594 : Nat := 51390969611055741473063

theorem tailTrace_112594 : CollatzResearch.WordTrace tailWord_112594 prefixEnd_112594 51390969611055741473063 := by
  unfold tailWord_112594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026660138524660592342209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2737760369399094912912557 1026660138524660592342209)
  ·
    refine ⟨769995103893495444256657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1026660138524660592342209 769995103893495444256657)
    ·
      refine ⟨577496327920121583192493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 769995103893495444256657 577496327920121583192493)
      ·
        refine ⟨216561122970045593697185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577496327920121583192493 216561122970045593697185)
        ·
          refine ⟨162420842227534195272889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216561122970045593697185 162420842227534195272889)
          ·
            refine ⟨121815631670650646454667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162420842227534195272889 121815631670650646454667)
            ·
              refine ⟨182723447505975969682001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121815631670650646454667 182723447505975969682001)
              ·
                refine ⟨137042585629481977261501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182723447505975969682001 137042585629481977261501)
                ·
                  refine ⟨51390969611055741473063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137042585629481977261501 51390969611055741473063)
                  ·
                    rfl

theorem cell20_112594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_112594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112594 prefixEnd_112594 := by exact prefixLift 112594
  have htrace : WordTrace (prefixWord ++ tailWord_112594) baseStart_112594 baseEnd_112594 := by
    simpa [prefixWord, tailWord_112594, baseEnd_112594] using wordTrace_append hprefix tailTrace_112594
  have hstable : (prefixWord ++ tailWord_112594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112594).length < 2 ^ (prefixWord ++ tailWord_112594).sum := by decide
  have hdescent : baseEnd_112594 < baseStart_112594 := by decide
  rcases family_descends (prefixWord ++ tailWord_112594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112619 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_112619 : Nat := 118140960795 + 112619 * 2 ^ 59
def prefixEnd_112619 : Nat := 4983230072969 + 3 ^ 40 * 112619 * 2
def baseEnd_112619 : Nat := 51402380292266765639627

theorem tailTrace_112619 : CollatzResearch.WordTrace tailWord_112619 prefixEnd_112619 51402380292266765639627 := by
  unfold tailWord_112619
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107552379008071639028911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2738368252672047759352607 4107552379008071639028911)
  ·
    refine ⟨6161328568512107458543367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4107552379008071639028911 6161328568512107458543367)
    ·
      refine ⟨9241992852768161187815051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6161328568512107458543367 9241992852768161187815051)
      ·
        refine ⟨13862989279152241781722577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9241992852768161187815051 13862989279152241781722577)
        ·
          refine ⟨10397241959364181336291933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13862989279152241781722577 10397241959364181336291933)
          ·
            refine ⟨3898965734761568001109475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10397241959364181336291933 3898965734761568001109475)
            ·
              refine ⟨5848448602142352001664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898965734761568001109475 5848448602142352001664213)
              ·
                refine ⟨137073014112711375039005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5848448602142352001664213 137073014112711375039005)
                ·
                  refine ⟨51402380292266765639627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137073014112711375039005 51402380292266765639627)
                  ·
                    rfl

theorem cell20_112619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_112619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112619 prefixEnd_112619 := by exact prefixLift 112619
  have htrace : WordTrace (prefixWord ++ tailWord_112619) baseStart_112619 baseEnd_112619 := by
    simpa [prefixWord, tailWord_112619, baseEnd_112619] using wordTrace_append hprefix tailTrace_112619
  have hstable : (prefixWord ++ tailWord_112619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112619).length < 2 ^ (prefixWord ++ tailWord_112619).sum := by decide
  have hdescent : baseEnd_112619 < baseStart_112619 := by decide
  rcases family_descends (prefixWord ++ tailWord_112619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112674 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_112674 : Nat := 118140960795 + 112674 * 2 ^ 59
def prefixEnd_112674 : Nat := 4983230072969 + 3 ^ 40 * 112674 * 2
def baseEnd_112674 : Nat := 51427483790931018806069

theorem tailTrace_112674 : CollatzResearch.WordTrace tailWord_112674 prefixEnd_112674 51427483790931018806069 := by
  unfold tailWord_112674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027389598452204008070269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2739705595872544021520717 1027389598452204008070269)
  ·
    refine ⟨385271099419576503026351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1027389598452204008070269 385271099419576503026351)
    ·
      refine ⟨577906649129364754539527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385271099419576503026351 577906649129364754539527)
      ·
        refine ⟨866859973694047131809291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577906649129364754539527 866859973694047131809291)
        ·
          refine ⟨1300289960541070697713937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866859973694047131809291 1300289960541070697713937)
          ·
            refine ⟨975217470405803023285453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300289960541070697713937 975217470405803023285453)
            ·
              refine ⟨365706551402176133732045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 975217470405803023285453 365706551402176133732045)
              ·
                refine ⟨137139956775816050149517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365706551402176133732045 137139956775816050149517)
                ·
                  refine ⟨51427483790931018806069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137139956775816050149517 51427483790931018806069)
                  ·
                    rfl

theorem cell20_112674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_112674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112674 prefixEnd_112674 := by exact prefixLift 112674
  have htrace : WordTrace (prefixWord ++ tailWord_112674) baseStart_112674 baseEnd_112674 := by
    simpa [prefixWord, tailWord_112674, baseEnd_112674] using wordTrace_append hprefix tailTrace_112674
  have hstable : (prefixWord ++ tailWord_112674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112674).length < 2 ^ (prefixWord ++ tailWord_112674).sum := by decide
  have hdescent : baseEnd_112674 < baseStart_112674 := by decide
  rcases family_descends (prefixWord ++ tailWord_112674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112719 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 2]
def baseStart_112719 : Nat := 118140960795 + 112719 * 2 ^ 59
def prefixEnd_112719 : Nat := 4983230072969 + 3 ^ 40 * 112719 * 2
def baseEnd_112719 : Nat := 51448023017110862305885

theorem tailTrace_112719 : CollatzResearch.WordTrace tailWord_112719 prefixEnd_112719 51448023017110862305885 := by
  unfold tailWord_112719
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111199678645788717669211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2740799785763859145112807 4111199678645788717669211)
  ·
    refine ⟨6166799517968683076503817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4111199678645788717669211 6166799517968683076503817)
    ·
      refine ⟨4625099638476512307377863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6166799517968683076503817 4625099638476512307377863)
      ·
        refine ⟨6937649457714768461066795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625099638476512307377863 6937649457714768461066795)
        ·
          refine ⟨10406474186572152691600193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937649457714768461066795 10406474186572152691600193)
          ·
            refine ⟨7804855639929114518700145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10406474186572152691600193 7804855639929114518700145)
            ·
              refine ⟨5853641729946835889025109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7804855639929114518700145 5853641729946835889025109)
              ·
                refine ⟨68597364022814483074513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5853641729946835889025109 68597364022814483074513)
                ·
                  refine ⟨51448023017110862305885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68597364022814483074513 51448023017110862305885)
                  ·
                    rfl

theorem cell20_112719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 2].length) (baseStart_112719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112719 prefixEnd_112719 := by exact prefixLift 112719
  have htrace : WordTrace (prefixWord ++ tailWord_112719) baseStart_112719 baseEnd_112719 := by
    simpa [prefixWord, tailWord_112719, baseEnd_112719] using wordTrace_append hprefix tailTrace_112719
  have hstable : (prefixWord ++ tailWord_112719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112719).length < 2 ^ (prefixWord ++ tailWord_112719).sum := by decide
  have hdescent : baseEnd_112719 < baseStart_112719 := by decide
  rcases family_descends (prefixWord ++ tailWord_112719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112722 : List Nat := [3, 2, 2, 1, 5, 1, 1, 5]
def baseStart_112722 : Nat := 118140960795 + 112722 * 2 ^ 59
def prefixEnd_112722 : Nat := 4983230072969 + 3 ^ 40 * 112722 * 2
def baseEnd_112722 : Nat := 17149797432952061735291

theorem tailTrace_112722 : CollatzResearch.WordTrace tailWord_112722 prefixEnd_112722 17149797432952061735291 := by
  unfold tailWord_112722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027827274408730057507105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2740872731756613486685613 1027827274408730057507105)
  ·
    refine ⟨770870455806547543130329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1027827274408730057507105 770870455806547543130329)
    ·
      refine ⟨578152841854910657347747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770870455806547543130329 578152841854910657347747)
      ·
        refine ⟨867229262782365986021621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578152841854910657347747 867229262782365986021621)
        ·
          refine ⟨81302743385846811189527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 867229262782365986021621 81302743385846811189527)
          ·
            refine ⟨121954115078770216784291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81302743385846811189527 121954115078770216784291)
            ·
              refine ⟨182931172618155325176437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121954115078770216784291 182931172618155325176437)
              ·
                refine ⟨17149797432952061735291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182931172618155325176437 17149797432952061735291)
                ·
                  rfl

theorem cell20_112722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_112722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112722 prefixEnd_112722 := by exact prefixLift 112722
  have htrace : WordTrace (prefixWord ++ tailWord_112722) baseStart_112722 baseEnd_112722 := by
    simpa [prefixWord, tailWord_112722, baseEnd_112722] using wordTrace_append hprefix tailTrace_112722
  have hstable : (prefixWord ++ tailWord_112722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112722).length < 2 ^ (prefixWord ++ tailWord_112722).sum := by decide
  have hdescent : baseEnd_112722 < baseStart_112722 := by decide
  rcases family_descends (prefixWord ++ tailWord_112722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112740 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_112740 : Nat := 118140960795 + 112740 * 2 ^ 59
def prefixEnd_112740 : Nat := 4983230072969 + 3 ^ 40 * 112740 * 2
def baseEnd_112740 : Nat := 51457607989328122605799

theorem tailTrace_112740 : CollatzResearch.WordTrace tailWord_112740 prefixEnd_112740 51457607989328122605799 := by
  unfold tailWord_112740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055982805784854652091837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2741310407713139536122449 2055982805784854652091837)
  ·
    refine ⟨770993552169320494534439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2055982805784854652091837 770993552169320494534439)
    ·
      refine ⟨1156490328253980741801659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770993552169320494534439 1156490328253980741801659)
      ·
        refine ⟨1734735492380971112702489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156490328253980741801659 1734735492380971112702489)
        ·
          refine ⟨1301051619285728334526867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734735492380971112702489 1301051619285728334526867)
          ·
            refine ⟨1951577428928592501790301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301051619285728334526867 1951577428928592501790301)
            ·
              refine ⟨731841535848222188171363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1951577428928592501790301 731841535848222188171363)
              ·
                refine ⟨1097762303772333282257045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731841535848222188171363 1097762303772333282257045)
                ·
                  refine ⟨51457607989328122605799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1097762303772333282257045 51457607989328122605799)
                  ·
                    rfl

theorem cell20_112740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_112740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112740 prefixEnd_112740 := by exact prefixLift 112740
  have htrace : WordTrace (prefixWord ++ tailWord_112740) baseStart_112740 baseEnd_112740 := by
    simpa [prefixWord, tailWord_112740, baseEnd_112740] using wordTrace_append hprefix tailTrace_112740
  have hstable : (prefixWord ++ tailWord_112740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112740).length < 2 ^ (prefixWord ++ tailWord_112740).sum := by decide
  have hdescent : baseEnd_112740 < baseStart_112740 := by decide
  rcases family_descends (prefixWord ++ tailWord_112740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112771 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_112771 : Nat := 118140960795 + 112771 * 2 ^ 59
def prefixEnd_112771 : Nat := 4983230072969 + 3 ^ 40 * 112771 * 2
def baseEnd_112771 : Nat := 51471757234029792572339

theorem tailTrace_112771 : CollatzResearch.WordTrace tailWord_112771 prefixEnd_112771 51471757234029792572339 := by
  unfold tailWord_112771
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113096274457401598562167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2742064182971601065708111 4113096274457401598562167)
  ·
    refine ⟨6169644411686102397843251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4113096274457401598562167 6169644411686102397843251)
    ·
      refine ⟨9254466617529153596764877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169644411686102397843251 9254466617529153596764877)
      ·
        refine ⟨3470424981573432598786829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9254466617529153596764877 3470424981573432598786829)
        ·
          refine ⟨1301409368090037224545061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3470424981573432598786829 1301409368090037224545061)
          ·
            refine ⟨244014256516881979602199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1301409368090037224545061 244014256516881979602199)
            ·
              refine ⟨366021384775322969403299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244014256516881979602199 366021384775322969403299)
              ·
                refine ⟨549032077162984454104949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366021384775322969403299 549032077162984454104949)
                ·
                  refine ⟨51471757234029792572339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 549032077162984454104949 51471757234029792572339)
                  ·
                    rfl

theorem cell20_112771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_112771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112771 prefixEnd_112771 := by exact prefixLift 112771
  have htrace : WordTrace (prefixWord ++ tailWord_112771) baseStart_112771 baseEnd_112771 := by
    simpa [prefixWord, tailWord_112771, baseEnd_112771] using wordTrace_append hprefix tailTrace_112771
  have hstable : (prefixWord ++ tailWord_112771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112771).length < 2 ^ (prefixWord ++ tailWord_112771).sum := by decide
  have hdescent : baseEnd_112771 < baseStart_112771 := by decide
  rcases family_descends (prefixWord ++ tailWord_112771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112790 : List Nat := [5, 3, 2, 1, 2, 1, 2, 4]
def baseStart_112790 : Nat := 118140960795 + 112790 * 2 ^ 59
def prefixEnd_112790 : Nat := 4983230072969 + 3 ^ 40 * 112790 * 2
def baseEnd_112790 : Nat := 17160143117250056979643

theorem tailTrace_112790 : CollatzResearch.WordTrace tailWord_112790 prefixEnd_112790 17160143117250056979643 := by
  unfold tailWord_112790
  simp only [CollatzResearch.WordTrace]
  refine ⟨257111828836785490218989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2742526174259045229002549 257111828836785490218989)
  ·
    refine ⟨96416935813794558832121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257111828836785490218989 96416935813794558832121)
    ·
      refine ⟨72312701860345919124091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96416935813794558832121 72312701860345919124091)
      ·
        refine ⟨108469052790518878686137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72312701860345919124091 108469052790518878686137)
        ·
          refine ⟨81351789592889159014603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108469052790518878686137 81351789592889159014603)
          ·
            refine ⟨122027684389333738521905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81351789592889159014603 122027684389333738521905)
            ·
              refine ⟨91520763292000303891429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122027684389333738521905 91520763292000303891429)
              ·
                refine ⟨17160143117250056979643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91520763292000303891429 17160143117250056979643)
                ·
                  rfl

theorem cell20_112790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_112790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112790 prefixEnd_112790 := by exact prefixLift 112790
  have htrace : WordTrace (prefixWord ++ tailWord_112790) baseStart_112790 baseEnd_112790 := by
    simpa [prefixWord, tailWord_112790, baseEnd_112790] using wordTrace_append hprefix tailTrace_112790
  have hstable : (prefixWord ++ tailWord_112790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112790).length < 2 ^ (prefixWord ++ tailWord_112790).sum := by decide
  have hdescent : baseEnd_112790 < baseStart_112790 := by decide
  rcases family_descends (prefixWord ++ tailWord_112790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112823 : List Nat := [1, 1, 3, 1, 4, 2, 8]
def baseStart_112823 : Nat := 118140960795 + 112823 * 2 ^ 59
def prefixEnd_112823 : Nat := 4983230072969 + 3 ^ 40 * 112823 * 2
def baseEnd_112823 : Nat := 5721721272327635870977

theorem tailTrace_112823 : CollatzResearch.WordTrace tailWord_112823 prefixEnd_112823 5721721272327635870977 := by
  unfold tailWord_112823
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114992870269014479455123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2743328580179342986303415 4114992870269014479455123)
  ·
    refine ⟨6172489305403521719182685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114992870269014479455123 6172489305403521719182685)
    ·
      refine ⟨2314683489526320644693507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6172489305403521719182685 2314683489526320644693507)
      ·
        refine ⟨3472025234289480967040261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314683489526320644693507 3472025234289480967040261)
        ·
          refine ⟨651004731429277681320049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3472025234289480967040261 651004731429277681320049)
          ·
            refine ⟨488253548571958260990037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651004731429277681320049 488253548571958260990037)
            ·
              refine ⟨5721721272327635870977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 488253548571958260990037 5721721272327635870977)
              ·
                rfl

theorem cell20_112823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_112823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112823 prefixEnd_112823 := by exact prefixLift 112823
  have htrace : WordTrace (prefixWord ++ tailWord_112823) baseStart_112823 baseEnd_112823 := by
    simpa [prefixWord, tailWord_112823, baseEnd_112823] using wordTrace_append hprefix tailTrace_112823
  have hstable : (prefixWord ++ tailWord_112823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112823).length < 2 ^ (prefixWord ++ tailWord_112823).sum := by decide
  have hdescent : baseEnd_112823 < baseStart_112823 := by decide
  rcases family_descends (prefixWord ++ tailWord_112823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112847 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_112847 : Nat := 118140960795 + 112847 * 2 ^ 59
def prefixEnd_112847 : Nat := 4983230072969 + 3 ^ 40 * 112847 * 2
def baseEnd_112847 : Nat := 51506445704911306038695

theorem tailTrace_112847 : CollatzResearch.WordTrace tailWord_112847 prefixEnd_112847 51506445704911306038695 := by
  unfold tailWord_112847
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115868222182066578328795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2743912148121377718885863 4115868222182066578328795)
  ·
    refine ⟨6173802333273099867493193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4115868222182066578328795 6173802333273099867493193)
    ·
      refine ⟨4630351749954824900619895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6173802333273099867493193 4630351749954824900619895)
      ·
        refine ⟨6945527624932237350929843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4630351749954824900619895 6945527624932237350929843)
        ·
          refine ⟨10418291437398356026394765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945527624932237350929843 10418291437398356026394765)
          ·
            refine ⟨3906859289024383509898037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10418291437398356026394765 3906859289024383509898037)
            ·
              refine ⟨366268058346035954052941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3906859289024383509898037 366268058346035954052941)
              ·
                refine ⟨137350521879763482769853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366268058346035954052941 137350521879763482769853)
                ·
                  refine ⟨51506445704911306038695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137350521879763482769853 51506445704911306038695)
                  ·
                    rfl

theorem cell20_112847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_112847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112847 prefixEnd_112847 := by exact prefixLift 112847
  have htrace : WordTrace (prefixWord ++ tailWord_112847) baseStart_112847 baseEnd_112847 := by
    simpa [prefixWord, tailWord_112847, baseEnd_112847] using wordTrace_append hprefix tailTrace_112847
  have hstable : (prefixWord ++ tailWord_112847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112847).length < 2 ^ (prefixWord ++ tailWord_112847).sum := by decide
  have hdescent : baseEnd_112847 < baseStart_112847 := by decide
  rcases family_descends (prefixWord ++ tailWord_112847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112936 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 3]
def baseStart_112936 : Nat := 118140960795 + 112936 * 2 ^ 59
def prefixEnd_112936 : Nat := 4983230072969 + 3 ^ 40 * 112936 * 2
def baseEnd_112936 : Nat := 51547067730022552071665

theorem tailTrace_112936 : CollatzResearch.WordTrace tailWord_112936 prefixEnd_112936 51547067730022552071665 := by
  unfold tailWord_112936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059557159429817389159331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2746076212573089852212441 2059557159429817389159331)
  ·
    refine ⟨3089335739144726083738997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2059557159429817389159331 3089335739144726083738997)
    ·
      refine ⟨289625225544818070350531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3089335739144726083738997 289625225544818070350531)
      ·
        refine ⟨434437838317227105525797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289625225544818070350531 434437838317227105525797)
        ·
          refine ⟨81457094684480082286087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434437838317227105525797 81457094684480082286087)
          ·
            refine ⟨122185642026720123429131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81457094684480082286087 122185642026720123429131)
            ·
              refine ⟨183278463040080185143697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122185642026720123429131 183278463040080185143697)
              ·
                refine ⟨137458847280060138857773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183278463040080185143697 137458847280060138857773)
                ·
                  refine ⟨51547067730022552071665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137458847280060138857773 51547067730022552071665)
                  ·
                    rfl

theorem cell20_112936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_112936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112936 prefixEnd_112936 := by exact prefixLift 112936
  have htrace : WordTrace (prefixWord ++ tailWord_112936) baseStart_112936 baseEnd_112936 := by
    simpa [prefixWord, tailWord_112936, baseEnd_112936] using wordTrace_append hprefix tailTrace_112936
  have hstable : (prefixWord ++ tailWord_112936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112936).length < 2 ^ (prefixWord ++ tailWord_112936).sum := by decide
  have hdescent : baseEnd_112936 < baseStart_112936 := by decide
  rcases family_descends (prefixWord ++ tailWord_112936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112947 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 2]
def baseStart_112947 : Nat := 118140960795 + 112947 * 2 ^ 59
def prefixEnd_112947 : Nat := 4983230072969 + 3 ^ 40 * 112947 * 2
def baseEnd_112947 : Nat := 51552088429755402704953

theorem tailTrace_112947 : CollatzResearch.WordTrace tailWord_112947 prefixEnd_112947 51552088429755402704953 := by
  unfold tailWord_112947
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119515521819783656969095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2746343681213189104646063 4119515521819783656969095)
  ·
    refine ⟨6179273282729675485453643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4119515521819783656969095 6179273282729675485453643)
    ·
      refine ⟨9268909924094513228180465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6179273282729675485453643 9268909924094513228180465)
      ·
        refine ⟨6951682443070884921135349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9268909924094513228180465 6951682443070884921135349)
        ·
          refine ⟨651720229037895461356439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6951682443070884921135349 651720229037895461356439)
          ·
            refine ⟨977580343556843192034659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651720229037895461356439 977580343556843192034659)
            ·
              refine ⟨1466370515335264788051989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977580343556843192034659 1466370515335264788051989)
              ·
                refine ⟨68736117906340536939937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1466370515335264788051989 68736117906340536939937)
                ·
                  refine ⟨51552088429755402704953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68736117906340536939937 51552088429755402704953)
                  ·
                    rfl

theorem cell20_112947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 2].length) (baseStart_112947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112947 prefixEnd_112947 := by exact prefixLift 112947
  have htrace : WordTrace (prefixWord ++ tailWord_112947) baseStart_112947 baseEnd_112947 := by
    simpa [prefixWord, tailWord_112947, baseEnd_112947] using wordTrace_append hprefix tailTrace_112947
  have hstable : (prefixWord ++ tailWord_112947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112947).length < 2 ^ (prefixWord ++ tailWord_112947).sum := by decide
  have hdescent : baseEnd_112947 < baseStart_112947 := by decide
  rcases family_descends (prefixWord ++ tailWord_112947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112968 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_112968 : Nat := 118140960795 + 112968 * 2 ^ 59
def prefixEnd_112968 : Nat := 4983230072969 + 3 ^ 40 * 112968 * 2
def baseEnd_112968 : Nat := 51561673401972663004867

theorem tailTrace_112968 : CollatzResearch.WordTrace tailWord_112968 prefixEnd_112968 51561673401972663004867 := by
  unfold tailWord_112968
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060140727371852121741779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2746854303162469495655705 2060140727371852121741779)
  ·
    refine ⟨3090211091057778182612669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060140727371852121741779 3090211091057778182612669)
    ·
      refine ⟨1158829159146666818479751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3090211091057778182612669 1158829159146666818479751)
      ·
        refine ⟨1738243738720000227719627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158829159146666818479751 1738243738720000227719627)
        ·
          refine ⟨2607365608080000341579441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738243738720000227719627 2607365608080000341579441)
          ·
            refine ⟨1955524206060000256184581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607365608080000341579441 1955524206060000256184581)
            ·
              refine ⟨366660788636250048034609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1955524206060000256184581 366660788636250048034609)
              ·
                refine ⟨274995591477187536025957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366660788636250048034609 274995591477187536025957)
                ·
                  refine ⟨51561673401972663004867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274995591477187536025957 51561673401972663004867)
                  ·
                    rfl

theorem cell20_112968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_112968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112968 prefixEnd_112968 := by exact prefixLift 112968
  have htrace : WordTrace (prefixWord ++ tailWord_112968) baseStart_112968 baseEnd_112968 := by
    simpa [prefixWord, tailWord_112968, baseEnd_112968] using wordTrace_append hprefix tailTrace_112968
  have hstable : (prefixWord ++ tailWord_112968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112968).length < 2 ^ (prefixWord ++ tailWord_112968).sum := by decide
  have hdescent : baseEnd_112968 < baseStart_112968 := by decide
  rcases family_descends (prefixWord ++ tailWord_112968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112981 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 2]
def baseStart_112981 : Nat := 118140960795 + 112981 * 2 ^ 59
def prefixEnd_112981 : Nat := 4983230072969 + 3 ^ 40 * 112981 * 2
def baseEnd_112981 : Nat := 51567606956202395571481

theorem tailTrace_112981 : CollatzResearch.WordTrace tailWord_112981 prefixEnd_112981 51567606956202395571481 := by
  unfold tailWord_112981
  simp only [CollatzResearch.WordTrace]
  refine ⟨4120755603696607463706797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2747170402464404975804531 4120755603696607463706797)
  ·
    refine ⟨1545283351386227798890049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4120755603696607463706797 1545283351386227798890049)
    ·
      refine ⟨1158962513539670849167537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1545283351386227798890049 1158962513539670849167537)
      ·
        refine ⟨869221885154753136875653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1158962513539670849167537 869221885154753136875653)
        ·
          refine ⟨162979103466516213164185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 869221885154753136875653 162979103466516213164185)
          ·
            refine ⟨122234327599887159873139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162979103466516213164185 122234327599887159873139)
            ·
              refine ⟨183351491399830739809709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122234327599887159873139 183351491399830739809709)
              ·
                refine ⟨68756809274936527428641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183351491399830739809709 68756809274936527428641)
                ·
                  refine ⟨51567606956202395571481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68756809274936527428641 51567606956202395571481)
                  ·
                    rfl

theorem cell20_112981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_112981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112981 prefixEnd_112981 := by exact prefixLift 112981
  have htrace : WordTrace (prefixWord ++ tailWord_112981) baseStart_112981 baseEnd_112981 := by
    simpa [prefixWord, tailWord_112981, baseEnd_112981] using wordTrace_append hprefix tailTrace_112981
  have hstable : (prefixWord ++ tailWord_112981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112981).length < 2 ^ (prefixWord ++ tailWord_112981).sum := by decide
  have hdescent : baseEnd_112981 < baseStart_112981 := by decide
  rcases family_descends (prefixWord ++ tailWord_112981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112988 : List Nat := [2, 2, 4, 3, 2, 1, 6]
def baseStart_112988 : Nat := 118140960795 + 112988 * 2 ^ 59
def prefixEnd_112988 : Nat := 4983230072969 + 3 ^ 40 * 112988 * 2
def baseEnd_112988 : Nat := 5730089105215720259791

theorem tailTrace_112988 : CollatzResearch.WordTrace tailWord_112988 prefixEnd_112988 5730089105215720259791 := by
  unfold tailWord_112988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060505457335623829605809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2747340609780831772807745 2060505457335623829605809)
  ·
    refine ⟨1545379093001717872204357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2060505457335623829605809 1545379093001717872204357)
    ·
      refine ⟨289758579937822101038317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1545379093001717872204357 289758579937822101038317)
      ·
        refine ⟨108659467476683287889369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289758579937822101038317 108659467476683287889369)
        ·
          refine ⟨81494600607512465917027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108659467476683287889369 81494600607512465917027)
          ·
            refine ⟨122241900911268698875541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81494600607512465917027 122241900911268698875541)
            ·
              refine ⟨5730089105215720259791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122241900911268698875541 5730089105215720259791)
              ·
                rfl

theorem cell20_112988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 6].length) (baseStart_112988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112988 prefixEnd_112988 := by exact prefixLift 112988
  have htrace : WordTrace (prefixWord ++ tailWord_112988) baseStart_112988 baseEnd_112988 := by
    simpa [prefixWord, tailWord_112988, baseEnd_112988] using wordTrace_append hprefix tailTrace_112988
  have hstable : (prefixWord ++ tailWord_112988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112988).length < 2 ^ (prefixWord ++ tailWord_112988).sum := by decide
  have hdescent : baseEnd_112988 < baseStart_112988 := by decide
  rcases family_descends (prefixWord ++ tailWord_112988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112992 : List Nat := [2, 1, 1, 3, 5, 2, 6]
def baseStart_112992 : Nat := 118140960795 + 112992 * 2 ^ 59
def prefixEnd_112992 : Nat := 4983230072969 + 3 ^ 40 * 112992 * 2
def baseEnd_112992 : Nat := 5730291961770582911641

theorem tailTrace_112992 : CollatzResearch.WordTrace tailWord_112992 prefixEnd_112992 5730291961770582911641 := by
  unfold tailWord_112992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060578403328378171178615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2747437871104504228238153 2060578403328378171178615)
  ·
    refine ⟨3090867604992567256767923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060578403328378171178615 3090867604992567256767923)
    ·
      refine ⟨4636301407488850885151885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3090867604992567256767923 4636301407488850885151885)
      ·
        refine ⟨1738613027808319081931957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4636301407488850885151885 1738613027808319081931957)
        ·
          refine ⟨162994971357029913931121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1738613027808319081931957 162994971357029913931121)
          ·
            refine ⟨122246228517772435448341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162994971357029913931121 122246228517772435448341)
            ·
              refine ⟨5730291961770582911641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122246228517772435448341 5730291961770582911641)
              ·
                rfl

theorem cell20_112992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 6].length) (baseStart_112992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112992 prefixEnd_112992 := by exact prefixLift 112992
  have htrace : WordTrace (prefixWord ++ tailWord_112992) baseStart_112992 baseEnd_112992 := by
    simpa [prefixWord, tailWord_112992, baseEnd_112992] using wordTrace_append hprefix tailTrace_112992
  have hstable : (prefixWord ++ tailWord_112992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112992).length < 2 ^ (prefixWord ++ tailWord_112992).sum := by decide
  have hdescent : baseEnd_112992 < baseStart_112992 := by decide
  rcases family_descends (prefixWord ++ tailWord_112992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112999 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_112999 : Nat := 118140960795 + 112999 * 2 ^ 59
def prefixEnd_112999 : Nat := 4983230072969 + 3 ^ 40 * 112999 * 2
def baseEnd_112999 : Nat := 51575822646674332971407

theorem tailTrace_112999 : CollatzResearch.WordTrace tailWord_112999 prefixEnd_112999 51575822646674332971407 := by
  unfold tailWord_112999
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121412117631396537862051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2747608078420931025241367 4121412117631396537862051)
  ·
    refine ⟨6182118176447094806793077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4121412117631396537862051 6182118176447094806793077)
    ·
      refine ⟨579573579041915138136851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6182118176447094806793077 579573579041915138136851)
      ·
        refine ⟨869360368562872707205277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579573579041915138136851 869360368562872707205277)
        ·
          refine ⟨326010138211077265201979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 869360368562872707205277 326010138211077265201979)
          ·
            refine ⟨489015207316615897802969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326010138211077265201979 489015207316615897802969)
            ·
              refine ⟨366761405487461923352227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489015207316615897802969 366761405487461923352227)
              ·
                refine ⟨550142108231192885028341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366761405487461923352227 550142108231192885028341)
                ·
                  refine ⟨51575822646674332971407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 550142108231192885028341 51575822646674332971407)
                  ·
                    rfl

theorem cell20_112999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_112999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_112999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_112999 prefixEnd_112999 := by exact prefixLift 112999
  have htrace : WordTrace (prefixWord ++ tailWord_112999) baseStart_112999 baseEnd_112999 := by
    simpa [prefixWord, tailWord_112999, baseEnd_112999] using wordTrace_append hprefix tailTrace_112999
  have hstable : (prefixWord ++ tailWord_112999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112999).length < 2 ^ (prefixWord ++ tailWord_112999).sum := by decide
  have hdescent : baseEnd_112999 < baseStart_112999 := by decide
  rcases family_descends (prefixWord ++ tailWord_112999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113002 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_113002 : Nat := 118140960795 + 113002 * 2 ^ 59
def prefixEnd_113002 : Nat := 4983230072969 + 3 ^ 40 * 113002 * 2
def baseEnd_113002 : Nat := 51577191928419655871395

theorem tailTrace_113002 : CollatzResearch.WordTrace tailWord_113002 prefixEnd_113002 51577191928419655871395 := by
  unfold tailWord_113002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030380384155132012555315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2747681024413685366814173 1030380384155132012555315)
  ·
    refine ⟨1545570576232698018832973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1030380384155132012555315 1545570576232698018832973)
    ·
      refine ⟨579588966087261757062365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1545570576232698018832973 579588966087261757062365)
      ·
        refine ⟨217345862282723158898387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579588966087261757062365 217345862282723158898387)
        ·
          refine ⟨326018793424084738347581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217345862282723158898387 326018793424084738347581)
          ·
            refine ⟨122257047534031776880343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326018793424084738347581 122257047534031776880343)
            ·
              refine ⟨183385571301047665320515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122257047534031776880343 183385571301047665320515)
              ·
                refine ⟨275078356951571497980773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183385571301047665320515 275078356951571497980773)
                ·
                  refine ⟨51577191928419655871395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275078356951571497980773 51577191928419655871395)
                  ·
                    rfl

theorem cell20_113002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_113002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113002 prefixEnd_113002 := by exact prefixLift 113002
  have htrace : WordTrace (prefixWord ++ tailWord_113002) baseStart_113002 baseEnd_113002 := by
    simpa [prefixWord, tailWord_113002, baseEnd_113002] using wordTrace_append hprefix tailTrace_113002
  have hstable : (prefixWord ++ tailWord_113002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113002).length < 2 ^ (prefixWord ++ tailWord_113002).sum := by decide
  have hdescent : baseEnd_113002 < baseStart_113002 := by decide
  rcases family_descends (prefixWord ++ tailWord_113002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113020 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_113020 : Nat := 118140960795 + 113020 * 2 ^ 59
def prefixEnd_113020 : Nat := 4983230072969 + 3 ^ 40 * 113020 * 2
def baseEnd_113020 : Nat := 51585407618891593271321

theorem tailTrace_113020 : CollatzResearch.WordTrace tailWord_113020 prefixEnd_113020 51585407618891593271321 := by
  unfold tailWord_113020
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061089025277658562188257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2748118700370211416251009 2061089025277658562188257)
  ·
    refine ⟨1545816768958243921641193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2061089025277658562188257 1545816768958243921641193)
    ·
      refine ⟨1159362576718682941230895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1545816768958243921641193 1159362576718682941230895)
      ·
        refine ⟨1739043865078024411846343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159362576718682941230895 1739043865078024411846343)
        ·
          refine ⟨2608565797617036617769515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739043865078024411846343 2608565797617036617769515)
          ·
            refine ⟨3912848696425554926654273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608565797617036617769515 3912848696425554926654273)
            ·
              refine ⟨2934636522319166194990705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3912848696425554926654273 2934636522319166194990705)
              ·
                refine ⟨2200977391739374646243029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934636522319166194990705 2200977391739374646243029)
                ·
                  refine ⟨51585407618891593271321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2200977391739374646243029 51585407618891593271321)
                  ·
                    rfl

theorem cell20_113020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_113020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113020 prefixEnd_113020 := by exact prefixLift 113020
  have htrace : WordTrace (prefixWord ++ tailWord_113020) baseStart_113020 baseEnd_113020 := by
    simpa [prefixWord, tailWord_113020, baseEnd_113020] using wordTrace_append hprefix tailTrace_113020
  have hstable : (prefixWord ++ tailWord_113020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113020).length < 2 ^ (prefixWord ++ tailWord_113020).sum := by decide
  have hdescent : baseEnd_113020 < baseStart_113020 := by decide
  rcases family_descends (prefixWord ++ tailWord_113020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113057 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 2]
def baseStart_113057 : Nat := 118140960795 + 113057 * 2 ^ 59
def prefixEnd_113057 : Nat := 4983230072969 + 3 ^ 40 * 113057 * 2
def baseEnd_113057 : Nat := 51602295427083909037837

theorem tailTrace_113057 : CollatzResearch.WordTrace tailWord_113057 prefixEnd_113057 51602295427083909037837 := by
  unfold tailWord_113057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123527551421272443473425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2749018367614181628982283 4123527551421272443473425)
  ·
    refine ⟨3092645663565954332605069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4123527551421272443473425 3092645663565954332605069)
    ·
      refine ⟨1159742123837232874726901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3092645663565954332605069 1159742123837232874726901)
      ·
        refine ⟨108725824109740582005647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1159742123837232874726901 108725824109740582005647)
        ·
          refine ⟨163088736164610873008471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108725824109740582005647 163088736164610873008471)
          ·
            refine ⟨244633104246916309512707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163088736164610873008471 244633104246916309512707)
            ·
              refine ⟨366949656370374464269061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244633104246916309512707 366949656370374464269061)
              ·
                refine ⟨68803060569445212050449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366949656370374464269061 68803060569445212050449)
                ·
                  refine ⟨51602295427083909037837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68803060569445212050449 51602295427083909037837)
                  ·
                    rfl

theorem cell20_113057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_113057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113057 prefixEnd_113057 := by exact prefixLift 113057
  have htrace : WordTrace (prefixWord ++ tailWord_113057) baseStart_113057 baseEnd_113057 := by
    simpa [prefixWord, tailWord_113057, baseEnd_113057] using wordTrace_append hprefix tailTrace_113057
  have hstable : (prefixWord ++ tailWord_113057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113057).length < 2 ^ (prefixWord ++ tailWord_113057).sum := by decide
  have hdescent : baseEnd_113057 < baseStart_113057 := by decide
  rcases family_descends (prefixWord ++ tailWord_113057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113061 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 2]
def baseStart_113061 : Nat := 118140960795 + 113061 * 2 ^ 59
def prefixEnd_113061 : Nat := 4983230072969 + 3 ^ 40 * 113061 * 2
def baseEnd_113061 : Nat := 51604121136077672904487

theorem tailTrace_113061 : CollatzResearch.WordTrace tailWord_113061 prefixEnd_113061 51604121136077672904487 := by
  unfold tailWord_113061
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123673443406781126619037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2749115628937854084412691 4123673443406781126619037)
  ·
    refine ⟨1546377541277542922482139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4123673443406781126619037 1546377541277542922482139)
    ·
      refine ⟨2319566311916314383723209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546377541277542922482139 2319566311916314383723209)
      ·
        refine ⟨1739674733937235787792407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319566311916314383723209 1739674733937235787792407)
        ·
          refine ⟨2609512100905853681688611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739674733937235787792407 2609512100905853681688611)
          ·
            refine ⟨3914268151358780522532917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609512100905853681688611 3914268151358780522532917)
            ·
              refine ⟨366962639189885673987461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3914268151358780522532917 366962639189885673987461)
              ·
                refine ⟨68805494848103563872649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366962639189885673987461 68805494848103563872649)
                ·
                  refine ⟨51604121136077672904487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68805494848103563872649 51604121136077672904487)
                  ·
                    rfl

theorem cell20_113061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_113061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113061 prefixEnd_113061 := by exact prefixLift 113061
  have htrace : WordTrace (prefixWord ++ tailWord_113061) baseStart_113061 baseEnd_113061 := by
    simpa [prefixWord, tailWord_113061, baseEnd_113061] using wordTrace_append hprefix tailTrace_113061
  have hstable : (prefixWord ++ tailWord_113061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113061).length < 2 ^ (prefixWord ++ tailWord_113061).sum := by decide
  have hdescent : baseEnd_113061 < baseStart_113061 := by decide
  rcases family_descends (prefixWord ++ tailWord_113061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113065 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_113065 : Nat := 118140960795 + 113065 * 2 ^ 59
def prefixEnd_113065 : Nat := 4983230072969 + 3 ^ 40 * 113065 * 2
def baseEnd_113065 : Nat := 51605946845071436771137

theorem tailTrace_113065 : CollatzResearch.WordTrace tailWord_113065 prefixEnd_113065 51605946845071436771137 := by
  unfold tailWord_113065
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123819335392289809764649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2749212890261526539843099 4123819335392289809764649)
  ·
    refine ⟨3092864501544217357323487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4123819335392289809764649 3092864501544217357323487)
    ·
      refine ⟨4639296752316326035985231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092864501544217357323487 4639296752316326035985231)
      ·
        refine ⟨6958945128474489053977847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639296752316326035985231 6958945128474489053977847)
        ·
          refine ⟨10438417692711733580966771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958945128474489053977847 10438417692711733580966771)
          ·
            refine ⟨15657626539067600371450157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10438417692711733580966771 15657626539067600371450157)
            ·
              refine ⟨5871609952150350139293809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15657626539067600371450157 5871609952150350139293809)
              ·
                refine ⟨4403707464112762604470357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5871609952150350139293809 4403707464112762604470357)
                ·
                  refine ⟨51605946845071436771137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4403707464112762604470357 51605946845071436771137)
                  ·
                    rfl

theorem cell20_113065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_113065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113065 prefixEnd_113065 := by exact prefixLift 113065
  have htrace : WordTrace (prefixWord ++ tailWord_113065) baseStart_113065 baseEnd_113065 := by
    simpa [prefixWord, tailWord_113065, baseEnd_113065] using wordTrace_append hprefix tailTrace_113065
  have hstable : (prefixWord ++ tailWord_113065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113065).length < 2 ^ (prefixWord ++ tailWord_113065).sum := by decide
  have hdescent : baseEnd_113065 < baseStart_113065 := by decide
  rcases family_descends (prefixWord ++ tailWord_113065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113103 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_113103 : Nat := 118140960795 + 113103 * 2 ^ 59
def prefixEnd_113103 : Nat := 4983230072969 + 3 ^ 40 * 113103 * 2
def baseEnd_113103 : Nat := 51623291080512193504315

theorem tailTrace_113103 : CollatzResearch.WordTrace tailWord_113103 prefixEnd_113103 51623291080512193504315 := by
  unfold tailWord_113103
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125205309254622299647963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2750136872836414866431975 4125205309254622299647963)
  ·
    refine ⟨6187807963881933449471945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4125205309254622299647963 6187807963881933449471945)
    ·
      refine ⟨4640855972911450087103959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6187807963881933449471945 4640855972911450087103959)
      ·
        refine ⟨6961283959367175130655939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640855972911450087103959 6961283959367175130655939)
        ·
          refine ⟨10441925939050762695983909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961283959367175130655939 10441925939050762695983909)
          ·
            refine ⟨1957861113572018005496983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10441925939050762695983909 1957861113572018005496983)
            ·
              refine ⟨2936791670358027008245475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957861113572018005496983 2936791670358027008245475)
              ·
                refine ⟨4405187505537040512368213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936791670358027008245475 4405187505537040512368213)
                ·
                  refine ⟨51623291080512193504315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4405187505537040512368213 51623291080512193504315)
                  ·
                    rfl

theorem cell20_113103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_113103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113103 prefixEnd_113103 := by exact prefixLift 113103
  have htrace : WordTrace (prefixWord ++ tailWord_113103) baseStart_113103 baseEnd_113103 := by
    simpa [prefixWord, tailWord_113103, baseEnd_113103] using wordTrace_append hprefix tailTrace_113103
  have hstable : (prefixWord ++ tailWord_113103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113103).length < 2 ^ (prefixWord ++ tailWord_113103).sum := by decide
  have hdescent : baseEnd_113103 < baseStart_113103 := by decide
  rcases family_descends (prefixWord ++ tailWord_113103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113120 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_113120 : Nat := 118140960795 + 113120 * 2 ^ 59
def prefixEnd_113120 : Nat := 4983230072969 + 3 ^ 40 * 113120 * 2
def baseEnd_113120 : Nat := 51631050343735689937579

theorem tailTrace_113120 : CollatzResearch.WordTrace tailWord_113120 prefixEnd_113120 51631050343735689937579 := by
  unfold tailWord_113120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062912675096517101508407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2750550233462022802011209 2062912675096517101508407)
  ·
    refine ⟨3094369012644775652262611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2062912675096517101508407 3094369012644775652262611)
    ·
      refine ⟨4641553518967163478393917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094369012644775652262611 4641553518967163478393917)
      ·
        refine ⟨1740582569612686304397719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4641553518967163478393917 1740582569612686304397719)
        ·
          refine ⟨2610873854419029456596579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740582569612686304397719 2610873854419029456596579)
          ·
            refine ⟨3916310781628544184894869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610873854419029456596579 3916310781628544184894869)
            ·
              refine ⟨183577067888838008666947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3916310781628544184894869 183577067888838008666947)
              ·
                refine ⟨275365601833257013000421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183577067888838008666947 275365601833257013000421)
                ·
                  refine ⟨51631050343735689937579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275365601833257013000421 51631050343735689937579)
                  ·
                    rfl

theorem cell20_113120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_113120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113120 prefixEnd_113120 := by exact prefixLift 113120
  have htrace : WordTrace (prefixWord ++ tailWord_113120) baseStart_113120 baseEnd_113120 := by
    simpa [prefixWord, tailWord_113120, baseEnd_113120] using wordTrace_append hprefix tailTrace_113120
  have hstable : (prefixWord ++ tailWord_113120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113120).length < 2 ^ (prefixWord ++ tailWord_113120).sum := by decide
  have hdescent : baseEnd_113120 < baseStart_113120 := by decide
  rcases family_descends (prefixWord ++ tailWord_113120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113127 : List Nat := [1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_113127 : Nat := 118140960795 + 113127 * 2 ^ 59
def prefixEnd_113127 : Nat := 4983230072969 + 3 ^ 40 * 113127 * 2
def baseEnd_113127 : Nat := 17211415111491592234739

theorem tailTrace_113127 : CollatzResearch.WordTrace tailWord_113127 prefixEnd_113127 17211415111491592234739 := by
  unfold tailWord_113127
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126080661167674398521635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2750720440778449599014423 4126080661167674398521635)
  ·
    refine ⟨6189120991751511597782453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4126080661167674398521635 6189120991751511597782453)
    ·
      refine ⟨580230092976704212292105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6189120991751511597782453 580230092976704212292105)
      ·
        refine ⟨435172569732528159219079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580230092976704212292105 435172569732528159219079)
        ·
          refine ⟨652758854598792238828619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435172569732528159219079 652758854598792238828619)
          ·
            refine ⟨979138281898188358242929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652758854598792238828619 979138281898188358242929)
            ·
              refine ⟨734353711423641268682197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979138281898188358242929 734353711423641268682197)
              ·
                refine ⟨17211415111491592234739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 734353711423641268682197 17211415111491592234739)
                ·
                  rfl

theorem cell20_113127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_113127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113127 prefixEnd_113127 := by exact prefixLift 113127
  have htrace : WordTrace (prefixWord ++ tailWord_113127) baseStart_113127 baseEnd_113127 := by
    simpa [prefixWord, tailWord_113127, baseEnd_113127] using wordTrace_append hprefix tailTrace_113127
  have hstable : (prefixWord ++ tailWord_113127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113127).length < 2 ^ (prefixWord ++ tailWord_113127).sum := by decide
  have hdescent : baseEnd_113127 < baseStart_113127 := by decide
  rcases family_descends (prefixWord ++ tailWord_113127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113230 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_113230 : Nat := 118140960795 + 113230 * 2 ^ 59
def prefixEnd_113230 : Nat := 4983230072969 + 3 ^ 40 * 113230 * 2
def baseEnd_113230 : Nat := 51681257341064196270463

theorem tailTrace_113230 : CollatzResearch.WordTrace tailWord_113230 prefixEnd_113230 51681257341064196270463 := by
  unfold tailWord_113230
  simp only [CollatzResearch.WordTrace]
  refine ⟨516229672474315373690143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2753224919863015326347429 516229672474315373690143)
  ·
    refine ⟨774344508711473060535215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516229672474315373690143 774344508711473060535215)
    ·
      refine ⟨1161516763067209590802823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774344508711473060535215 1161516763067209590802823)
      ·
        refine ⟨1742275144600814386204235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161516763067209590802823 1742275144600814386204235)
        ·
          refine ⟨2613412716901221579306353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742275144600814386204235 2613412716901221579306353)
          ·
            refine ⟨1960059537675916184479765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2613412716901221579306353 1960059537675916184479765)
            ·
              refine ⟨91877790828558571147489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1960059537675916184479765 91877790828558571147489)
              ·
                refine ⟨68908343121418928360617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91877790828558571147489 68908343121418928360617)
                ·
                  refine ⟨51681257341064196270463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68908343121418928360617 51681257341064196270463)
                  ·
                    rfl

theorem cell20_113230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_113230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113230 prefixEnd_113230 := by exact prefixLift 113230
  have htrace : WordTrace (prefixWord ++ tailWord_113230) baseStart_113230 baseEnd_113230 := by
    simpa [prefixWord, tailWord_113230, baseEnd_113230] using wordTrace_append hprefix tailTrace_113230
  have hstable : (prefixWord ++ tailWord_113230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113230).length < 2 ^ (prefixWord ++ tailWord_113230).sum := by decide
  have hdescent : baseEnd_113230 < baseStart_113230 := by decide
  rcases family_descends (prefixWord ++ tailWord_113230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113234 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_113234 : Nat := 118140960795 + 113234 * 2 ^ 59
def prefixEnd_113234 : Nat := 4983230072969 + 3 ^ 40 * 113234 * 2
def baseEnd_113234 : Nat := 51683083050057960137113

theorem tailTrace_113234 : CollatzResearch.WordTrace tailWord_113234 prefixEnd_113234 51683083050057960137113 := by
  unfold tailWord_113234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032495817945007918166689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2753322181186687781777837 1032495817945007918166689)
  ·
    refine ⟨774371863458755938625017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1032495817945007918166689 774371863458755938625017)
    ·
      refine ⟨580778897594066953968763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774371863458755938625017 580778897594066953968763)
      ·
        refine ⟨871168346391100430953145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580778897594066953968763 871168346391100430953145)
        ·
          refine ⟨653376259793325323214859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871168346391100430953145 653376259793325323214859)
          ·
            refine ⟨980064389689987984822289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653376259793325323214859 980064389689987984822289)
            ·
              refine ⟨735048292267490988616717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980064389689987984822289 735048292267490988616717)
              ·
                refine ⟨275643109600309120731269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 735048292267490988616717 275643109600309120731269)
                ·
                  refine ⟨51683083050057960137113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275643109600309120731269 51683083050057960137113)
                  ·
                    rfl

theorem cell20_113234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_113234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113234 prefixEnd_113234 := by exact prefixLift 113234
  have htrace : WordTrace (prefixWord ++ tailWord_113234) baseStart_113234 baseEnd_113234 := by
    simpa [prefixWord, tailWord_113234, baseEnd_113234] using wordTrace_append hprefix tailTrace_113234
  have hstable : (prefixWord ++ tailWord_113234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113234).length < 2 ^ (prefixWord ++ tailWord_113234).sum := by decide
  have hdescent : baseEnd_113234 < baseStart_113234 := by decide
  rcases family_descends (prefixWord ++ tailWord_113234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113258 : List Nat := [3, 1, 3, 2, 1, 1, 5, 4]
def baseStart_113258 : Nat := 118140960795 + 113258 * 2 ^ 59
def prefixEnd_113258 : Nat := 4983230072969 + 3 ^ 40 * 113258 * 2
def baseEnd_113258 : Nat := 17231345768006847779005

theorem tailTrace_113258 : CollatzResearch.WordTrace tailWord_113258 prefixEnd_113258 17231345768006847779005 := by
  unfold tailWord_113258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032714655923270942885107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2753905749128722514360285 1032714655923270942885107)
  ·
    refine ⟨1549071983884906414327661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1032714655923270942885107 1549071983884906414327661)
    ·
      refine ⟨580901993956839905372873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1549071983884906414327661 580901993956839905372873)
      ·
        refine ⟨435676495467629929029655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580901993956839905372873 435676495467629929029655)
        ·
          refine ⟨653514743201444893544483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435676495467629929029655 653514743201444893544483)
          ·
            refine ⟨980272114802167340316725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653514743201444893544483 980272114802167340316725)
            ·
              refine ⟨91900510762703188154693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 980272114802167340316725 91900510762703188154693)
              ·
                refine ⟨17231345768006847779005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91900510762703188154693 17231345768006847779005)
                ·
                  rfl

theorem cell20_113258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_113258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113258 prefixEnd_113258 := by exact prefixLift 113258
  have htrace : WordTrace (prefixWord ++ tailWord_113258) baseStart_113258 baseEnd_113258 := by
    simpa [prefixWord, tailWord_113258, baseEnd_113258] using wordTrace_append hprefix tailTrace_113258
  have hstable : (prefixWord ++ tailWord_113258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113258).length < 2 ^ (prefixWord ++ tailWord_113258).sum := by decide
  have hdescent : baseEnd_113258 < baseStart_113258 := by decide
  rcases family_descends (prefixWord ++ tailWord_113258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113313 : List Nat := [1, 2, 3, 3, 3, 2, 2, 4]
def baseStart_113313 : Nat := 118140960795 + 113313 * 2 ^ 59
def prefixEnd_113313 : Nat := 4983230072969 + 3 ^ 40 * 113313 * 2
def baseEnd_113313 : Nat := 17239713600894932167819

theorem tailTrace_113313 : CollatzResearch.WordTrace tailWord_113313 prefixEnd_113313 17239713600894932167819 := by
  unfold tailWord_113313
  simp only [CollatzResearch.WordTrace]
  refine ⟨4132864638493828164792593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2755243092329218776528395 4132864638493828164792593)
  ·
    refine ⟨3099648478870371123594445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4132864638493828164792593 3099648478870371123594445)
    ·
      refine ⟨1162368179576389171347917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3099648478870371123594445 1162368179576389171347917)
      ·
        refine ⟨435888067341145939255469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1162368179576389171347917 435888067341145939255469)
        ·
          refine ⟨163458025252929727220801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435888067341145939255469 163458025252929727220801)
          ·
            refine ⟨122593518939697295415601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163458025252929727220801 122593518939697295415601)
            ·
              refine ⟨91945139204772971561701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122593518939697295415601 91945139204772971561701)
              ·
                refine ⟨17239713600894932167819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91945139204772971561701 17239713600894932167819)
                ·
                  rfl

theorem cell20_113313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_113313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113313 prefixEnd_113313 := by exact prefixLift 113313
  have htrace : WordTrace (prefixWord ++ tailWord_113313) baseStart_113313 baseEnd_113313 := by
    simpa [prefixWord, tailWord_113313, baseEnd_113313] using wordTrace_append hprefix tailTrace_113313
  have hstable : (prefixWord ++ tailWord_113313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113313).length < 2 ^ (prefixWord ++ tailWord_113313).sum := by decide
  have hdescent : baseEnd_113313 < baseStart_113313 := by decide
  rcases family_descends (prefixWord ++ tailWord_113313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113327 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 2]
def baseStart_113327 : Nat := 118140960795 + 113327 * 2 ^ 59
def prefixEnd_113327 : Nat := 4983230072969 + 3 ^ 40 * 113327 * 2
def baseEnd_113327 : Nat := 51725530784162970036733

theorem tailTrace_113327 : CollatzResearch.WordTrace tailWord_113327 prefixEnd_113327 51725530784162970036733 := by
  unfold tailWord_113327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133375260443108555802235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2755583506962072370534823 4133375260443108555802235)
  ·
    refine ⟨6200062890664662833703353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133375260443108555802235 6200062890664662833703353)
    ·
      refine ⟨4650047167998497125277515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6200062890664662833703353 4650047167998497125277515)
      ·
        refine ⟨6975070751997745687916273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650047167998497125277515 6975070751997745687916273)
        ·
          refine ⟨5231303063998309265937205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6975070751997745687916273 5231303063998309265937205)
          ·
            refine ⟨490434662249841493681613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5231303063998309265937205 490434662249841493681613)
            ·
              refine ⟨183912998343690560130605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490434662249841493681613 183912998343690560130605)
              ·
                refine ⟨68967374378883960048977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183912998343690560130605 68967374378883960048977)
                ·
                  refine ⟨51725530784162970036733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68967374378883960048977 51725530784162970036733)
                  ·
                    rfl

theorem cell20_113327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 2].length) (baseStart_113327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113327 prefixEnd_113327 := by exact prefixLift 113327
  have htrace : WordTrace (prefixWord ++ tailWord_113327) baseStart_113327 baseEnd_113327 := by
    simpa [prefixWord, tailWord_113327, baseEnd_113327] using wordTrace_append hprefix tailTrace_113327
  have hstable : (prefixWord ++ tailWord_113327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113327).length < 2 ^ (prefixWord ++ tailWord_113327).sum := by decide
  have hdescent : baseEnd_113327 < baseStart_113327 := by decide
  rcases family_descends (prefixWord ++ tailWord_113327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113344 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 2]
def baseStart_113344 : Nat := 118140960795 + 113344 * 2 ^ 59
def prefixEnd_113344 : Nat := 4983230072969 + 3 ^ 40 * 113344 * 2
def baseEnd_113344 : Nat := 51733290047386466469997

theorem tailTrace_113344 : CollatzResearch.WordTrace tailWord_113344 prefixEnd_113344 51733290047386466469997 := by
  unfold tailWord_113344
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066997650690760229585543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2755996867587680306114057 2066997650690760229585543)
  ·
    refine ⟨3100496476036140344378315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2066997650690760229585543 3100496476036140344378315)
    ·
      refine ⟨4650744714054210516567473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100496476036140344378315 4650744714054210516567473)
      ·
        refine ⟨3488058535540657887425605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4650744714054210516567473 3488058535540657887425605)
        ·
          refine ⟨654010975413873353892301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3488058535540657887425605 654010975413873353892301)
          ·
            refine ⟨245254115780202507709613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 654010975413873353892301 245254115780202507709613)
            ·
              refine ⟨91970293417575940391105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245254115780202507709613 91970293417575940391105)
              ·
                refine ⟨68977720063181955293329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91970293417575940391105 68977720063181955293329)
                ·
                  refine ⟨51733290047386466469997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68977720063181955293329 51733290047386466469997)
                  ·
                    rfl

theorem cell20_113344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_113344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113344 prefixEnd_113344 := by exact prefixLift 113344
  have htrace : WordTrace (prefixWord ++ tailWord_113344) baseStart_113344 baseEnd_113344 := by
    simpa [prefixWord, tailWord_113344, baseEnd_113344] using wordTrace_append hprefix tailTrace_113344
  have hstable : (prefixWord ++ tailWord_113344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113344).length < 2 ^ (prefixWord ++ tailWord_113344).sum := by decide
  have hdescent : baseEnd_113344 < baseStart_113344 := by decide
  rcases family_descends (prefixWord ++ tailWord_113344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113350 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_113350 : Nat := 118140960795 + 113350 * 2 ^ 59
def prefixEnd_113350 : Nat := 4983230072969 + 3 ^ 40 * 113350 * 2
def baseEnd_113350 : Nat := 51736028610877112269973

theorem tailTrace_113350 : CollatzResearch.WordTrace tailWord_113350 prefixEnd_113350 51736028610877112269973 := by
  unfold tailWord_113350
  simp only [CollatzResearch.WordTrace]
  refine ⟨129194191854993233871547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2756142759573188989259669 129194191854993233871547)
  ·
    refine ⟨193791287782489850807321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129194191854993233871547 193791287782489850807321)
    ·
      refine ⟨145343465836867388105491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193791287782489850807321 145343465836867388105491)
      ·
        refine ⟨218015198755301082158237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145343465836867388105491 218015198755301082158237)
        ·
          refine ⟨81755699533237905809339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218015198755301082158237 81755699533237905809339)
          ·
            refine ⟨122633549299856858714009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81755699533237905809339 122633549299856858714009)
            ·
              refine ⟨91975161974892644035507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122633549299856858714009 91975161974892644035507)
              ·
                refine ⟨137962742962338966053261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91975161974892644035507 137962742962338966053261)
                ·
                  refine ⟨51736028610877112269973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137962742962338966053261 51736028610877112269973)
                  ·
                    rfl

theorem cell20_113350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_113350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113350 prefixEnd_113350 := by exact prefixLift 113350
  have htrace : WordTrace (prefixWord ++ tailWord_113350) baseStart_113350 baseEnd_113350 := by
    simpa [prefixWord, tailWord_113350, baseEnd_113350] using wordTrace_append hprefix tailTrace_113350
  have hstable : (prefixWord ++ tailWord_113350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113350).length < 2 ^ (prefixWord ++ tailWord_113350).sum := by decide
  have hdescent : baseEnd_113350 < baseStart_113350 := by decide
  rcases family_descends (prefixWord ++ tailWord_113350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113358 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_113358 : Nat := 118140960795 + 113358 * 2 ^ 59
def prefixEnd_113358 : Nat := 4983230072969 + 3 ^ 40 * 113358 * 2
def baseEnd_113358 : Nat := 51739680028864640003273

theorem tailTrace_113358 : CollatzResearch.WordTrace tailWord_113358 prefixEnd_113358 51739680028864640003273 := by
  unfold tailWord_113358
  simp only [CollatzResearch.WordTrace]
  refine ⟨516813240416350106272591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2756337282220533900120485 516813240416350106272591)
  ·
    refine ⟨775219860624525159408887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516813240416350106272591 775219860624525159408887)
    ·
      refine ⟨1162829790936787739113331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775219860624525159408887 1162829790936787739113331)
      ·
        refine ⟨1744244686405181608669997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162829790936787739113331 1744244686405181608669997)
        ·
          refine ⟨654091757401943103251249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1744244686405181608669997 654091757401943103251249)
          ·
            refine ⟨490568818051457327438437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654091757401943103251249 490568818051457327438437)
            ·
              refine ⟨91981653384648248894707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490568818051457327438437 91981653384648248894707)
              ·
                refine ⟨137972480076972373342061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91981653384648248894707 137972480076972373342061)
                ·
                  refine ⟨51739680028864640003273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137972480076972373342061 51739680028864640003273)
                  ·
                    rfl

theorem cell20_113358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_113358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113358 prefixEnd_113358 := by exact prefixLift 113358
  have htrace : WordTrace (prefixWord ++ tailWord_113358) baseStart_113358 baseEnd_113358 := by
    simpa [prefixWord, tailWord_113358, baseEnd_113358] using wordTrace_append hprefix tailTrace_113358
  have hstable : (prefixWord ++ tailWord_113358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113358).length < 2 ^ (prefixWord ++ tailWord_113358).sum := by decide
  have hdescent : baseEnd_113358 < baseStart_113358 := by decide
  rcases family_descends (prefixWord ++ tailWord_113358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113369 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_113369 : Nat := 118140960795 + 113369 * 2 ^ 59
def prefixEnd_113369 : Nat := 4983230072969 + 3 ^ 40 * 113369 * 2
def baseEnd_113369 : Nat := 51744700728597490636561

theorem tailTrace_113369 : CollatzResearch.WordTrace tailWord_113369 prefixEnd_113369 51744700728597490636561 := by
  unfold tailWord_113369
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134907126290949728831161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2756604750860633152554107 4134907126290949728831161)
  ·
    refine ⟨3101180344718212296623371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4134907126290949728831161 3101180344718212296623371)
    ·
      refine ⟨4651770517077318444935057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101180344718212296623371 4651770517077318444935057)
      ·
        refine ⟨3488827887807988833701293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4651770517077318444935057 3488827887807988833701293)
        ·
          refine ⟨1308310457927995812637985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3488827887807988833701293 1308310457927995812637985)
          ·
            refine ⟨981232843445996859478489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308310457927995812637985 981232843445996859478489)
            ·
              refine ⟨735924632584497644608867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981232843445996859478489 735924632584497644608867)
              ·
                refine ⟨1103886948876746466913301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735924632584497644608867 1103886948876746466913301)
                ·
                  refine ⟨51744700728597490636561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1103886948876746466913301 51744700728597490636561)
                  ·
                    rfl

theorem cell20_113369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_113369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113369 prefixEnd_113369 := by exact prefixLift 113369
  have htrace : WordTrace (prefixWord ++ tailWord_113369) baseStart_113369 baseEnd_113369 := by
    simpa [prefixWord, tailWord_113369, baseEnd_113369] using wordTrace_append hprefix tailTrace_113369
  have hstable : (prefixWord ++ tailWord_113369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113369).length < 2 ^ (prefixWord ++ tailWord_113369).sum := by decide
  have hdescent : baseEnd_113369 < baseStart_113369 := by decide
  rcases family_descends (prefixWord ++ tailWord_113369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113372 : List Nat := [2, 2, 5, 1, 1, 1, 2, 6]
def baseStart_113372 : Nat := 118140960795 + 113372 * 2 ^ 59
def prefixEnd_113372 : Nat := 4983230072969 + 3 ^ 40 * 113372 * 2
def baseEnd_113372 : Nat := 17248690003447604512183

theorem tailTrace_113372 : CollatzResearch.WordTrace tailWord_113372 prefixEnd_113372 17248690003447604512183 := by
  unfold tailWord_113372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067508272640040620595185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2756677696853387494126913 2067508272640040620595185)
  ·
    refine ⟨1550631204480030465446389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2067508272640040620595185 1550631204480030465446389)
    ·
      refine ⟨145371675420002856135599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1550631204480030465446389 145371675420002856135599)
      ·
        refine ⟨218057513130004284203399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145371675420002856135599 218057513130004284203399)
        ·
          refine ⟨327086269695006426305099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218057513130004284203399 327086269695006426305099)
          ·
            refine ⟨490629404542509639457649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327086269695006426305099 490629404542509639457649)
            ·
              refine ⟨367972053406882229593237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490629404542509639457649 367972053406882229593237)
              ·
                refine ⟨17248690003447604512183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367972053406882229593237 17248690003447604512183)
                ·
                  rfl

theorem cell20_113372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_113372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113372 prefixEnd_113372 := by exact prefixLift 113372
  have htrace : WordTrace (prefixWord ++ tailWord_113372) baseStart_113372 baseEnd_113372 := by
    simpa [prefixWord, tailWord_113372, baseEnd_113372] using wordTrace_append hprefix tailTrace_113372
  have hstable : (prefixWord ++ tailWord_113372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113372).length < 2 ^ (prefixWord ++ tailWord_113372).sum := by decide
  have hdescent : baseEnd_113372 < baseStart_113372 := by decide
  rcases family_descends (prefixWord ++ tailWord_113372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113407 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_113407 : Nat := 118140960795 + 113407 * 2 ^ 59
def prefixEnd_113407 : Nat := 4983230072969 + 3 ^ 40 * 113407 * 2
def baseEnd_113407 : Nat := 51762044964038247369739

theorem tailTrace_113407 : CollatzResearch.WordTrace tailWord_113407 prefixEnd_113407 51762044964038247369739 := by
  unfold tailWord_113407
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136293100153282218714475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2757528733435521479142983 4136293100153282218714475)
  ·
    refine ⟨6204439650229923328071713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4136293100153282218714475 6204439650229923328071713)
    ·
      refine ⟨4653329737672442496053785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6204439650229923328071713 4653329737672442496053785)
      ·
        refine ⟨3489997303254331872040339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653329737672442496053785 3489997303254331872040339)
        ·
          refine ⟨5234995954881497808060509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489997303254331872040339 5234995954881497808060509)
          ·
            refine ⟨1963123483080561678022691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5234995954881497808060509 1963123483080561678022691)
            ·
              refine ⟨2944685224620842517034037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963123483080561678022691 2944685224620842517034037)
              ·
                refine ⟨276064239808203985971941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2944685224620842517034037 276064239808203985971941)
                ·
                  refine ⟨51762044964038247369739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276064239808203985971941 51762044964038247369739)
                  ·
                    rfl

theorem cell20_113407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_113407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113407 prefixEnd_113407 := by exact prefixLift 113407
  have htrace : WordTrace (prefixWord ++ tailWord_113407) baseStart_113407 baseEnd_113407 := by
    simpa [prefixWord, tailWord_113407, baseEnd_113407] using wordTrace_append hprefix tailTrace_113407
  have hstable : (prefixWord ++ tailWord_113407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113407).length < 2 ^ (prefixWord ++ tailWord_113407).sum := by decide
  have hdescent : baseEnd_113407 < baseStart_113407 := by decide
  rcases family_descends (prefixWord ++ tailWord_113407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113410 : List Nat := [3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_113410 : Nat := 118140960795 + 113410 * 2 ^ 59
def prefixEnd_113410 : Nat := 4983230072969 + 3 ^ 40 * 113410 * 2
def baseEnd_113410 : Nat := 17254471415261190089909

theorem tailTrace_113410 : CollatzResearch.WordTrace tailWord_113410 prefixEnd_113410 17254471415261190089909 := by
  unfold tailWord_113410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034100629785603432768421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2757601679428275820715789 1034100629785603432768421)
  ·
    refine ⟨193893868084800643644079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1034100629785603432768421 193893868084800643644079)
    ·
      refine ⟨290840802127200965466119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193893868084800643644079 290840802127200965466119)
      ·
        refine ⟨436261203190801448199179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290840802127200965466119 436261203190801448199179)
        ·
          refine ⟨654391804786202172298769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436261203190801448199179 654391804786202172298769)
          ·
            refine ⟨490793853589651629224077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654391804786202172298769 490793853589651629224077)
            ·
              refine ⟨184047695096119360959029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490793853589651629224077 184047695096119360959029)
              ·
                refine ⟨17254471415261190089909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184047695096119360959029 17254471415261190089909)
                ·
                  rfl

theorem cell20_113410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_113410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113410 prefixEnd_113410 := by exact prefixLift 113410
  have htrace : WordTrace (prefixWord ++ tailWord_113410) baseStart_113410 baseEnd_113410 := by
    simpa [prefixWord, tailWord_113410, baseEnd_113410] using wordTrace_append hprefix tailTrace_113410
  have hstable : (prefixWord ++ tailWord_113410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113410).length < 2 ^ (prefixWord ++ tailWord_113410).sum := by decide
  have hdescent : baseEnd_113410 < baseStart_113410 := by decide
  rcases family_descends (prefixWord ++ tailWord_113410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113437 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 2]
def baseStart_113437 : Nat := 118140960795 + 113437 * 2 ^ 59
def prefixEnd_113437 : Nat := 4983230072969 + 3 ^ 40 * 113437 * 2
def baseEnd_113437 : Nat := 51775737781491476369617

theorem tailTrace_113437 : CollatzResearch.WordTrace tailWord_113437 prefixEnd_113437 51775737781491476369617 := by
  unfold tailWord_113437
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137387290044597342306565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2758258193363064894871043 4137387290044597342306565)
  ·
    refine ⟨775760116883362001682481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4137387290044597342306565 775760116883362001682481)
    ·
      refine ⟨581820087662521501261861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 775760116883362001682481 581820087662521501261861)
      ·
        refine ⟨109091266436722781486599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 581820087662521501261861 109091266436722781486599)
        ·
          refine ⟨163636899655084172229899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109091266436722781486599 163636899655084172229899)
          ·
            refine ⟨245455349482626258344849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163636899655084172229899 245455349482626258344849)
            ·
              refine ⟨184091512111969693758637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245455349482626258344849 184091512111969693758637)
              ·
                refine ⟨69034317041988635159489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184091512111969693758637 69034317041988635159489)
                ·
                  refine ⟨51775737781491476369617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69034317041988635159489 51775737781491476369617)
                  ·
                    rfl

theorem cell20_113437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_113437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113437 prefixEnd_113437 := by exact prefixLift 113437
  have htrace : WordTrace (prefixWord ++ tailWord_113437) baseStart_113437 baseEnd_113437 := by
    simpa [prefixWord, tailWord_113437, baseEnd_113437] using wordTrace_append hprefix tailTrace_113437
  have hstable : (prefixWord ++ tailWord_113437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113437).length < 2 ^ (prefixWord ++ tailWord_113437).sum := by decide
  have hdescent : baseEnd_113437 < baseStart_113437 := by decide
  rcases family_descends (prefixWord ++ tailWord_113437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113441 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 2]
def baseStart_113441 : Nat := 118140960795 + 113441 * 2 ^ 59
def prefixEnd_113441 : Nat := 4983230072969 + 3 ^ 40 * 113441 * 2
def baseEnd_113441 : Nat := 51777563490485240236267

theorem tailTrace_113441 : CollatzResearch.WordTrace tailWord_113441 prefixEnd_113441 51777563490485240236267 := by
  unfold tailWord_113441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137533182030106025452177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2758355454686737350301451 4137533182030106025452177)
  ·
    refine ⟨3103149886522579519089133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4137533182030106025452177 3103149886522579519089133)
    ·
      refine ⟨1163681207445967319658425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3103149886522579519089133 1163681207445967319658425)
      ·
        refine ⟨872760905584475489743819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1163681207445967319658425 872760905584475489743819)
        ·
          refine ⟨1309141358376713234615729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872760905584475489743819 1309141358376713234615729)
          ·
            refine ⟨981856018782534925961797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309141358376713234615729 981856018782534925961797)
            ·
              refine ⟨184098003521725298617837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 981856018782534925961797 184098003521725298617837)
              ·
                refine ⟨69036751320646986981689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184098003521725298617837 69036751320646986981689)
                ·
                  refine ⟨51777563490485240236267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69036751320646986981689 51777563490485240236267)
                  ·
                    rfl

theorem cell20_113441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_113441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113441 prefixEnd_113441 := by exact prefixLift 113441
  have htrace : WordTrace (prefixWord ++ tailWord_113441) baseStart_113441 baseEnd_113441 := by
    simpa [prefixWord, tailWord_113441, baseEnd_113441] using wordTrace_append hprefix tailTrace_113441
  have hstable : (prefixWord ++ tailWord_113441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113441).length < 2 ^ (prefixWord ++ tailWord_113441).sum := by decide
  have hdescent : baseEnd_113441 < baseStart_113441 := by decide
  rcases family_descends (prefixWord ++ tailWord_113441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113445 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_113445 : Nat := 118140960795 + 113445 * 2 ^ 59
def prefixEnd_113445 : Nat := 4983230072969 + 3 ^ 40 * 113445 * 2
def baseEnd_113445 : Nat := 51779389199479004102917

theorem tailTrace_113445 : CollatzResearch.WordTrace tailWord_113445 prefixEnd_113445 51779389199479004102917 := by
  unfold tailWord_113445
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137679074015614708597789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2758452716010409805731859 4137679074015614708597789)
  ·
    refine ⟨1551629652755855515724171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4137679074015614708597789 1551629652755855515724171)
    ·
      refine ⟨2327444479133783273586257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551629652755855515724171 2327444479133783273586257)
      ·
        refine ⟨1745583359350337455189693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2327444479133783273586257 1745583359350337455189693)
        ·
          refine ⟨654593759756376545696135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1745583359350337455189693 654593759756376545696135)
          ·
            refine ⟨981890639634564818544203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654593759756376545696135 981890639634564818544203)
            ·
              refine ⟨1472835959451847227816305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981890639634564818544203 1472835959451847227816305)
              ·
                refine ⟨1104626969588885420862229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472835959451847227816305 1104626969588885420862229)
                ·
                  refine ⟨51779389199479004102917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1104626969588885420862229 51779389199479004102917)
                  ·
                    rfl

theorem cell20_113445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_113445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113445 prefixEnd_113445 := by exact prefixLift 113445
  have htrace : WordTrace (prefixWord ++ tailWord_113445) baseStart_113445 baseEnd_113445 := by
    simpa [prefixWord, tailWord_113445, baseEnd_113445] using wordTrace_append hprefix tailTrace_113445
  have hstable : (prefixWord ++ tailWord_113445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113445).length < 2 ^ (prefixWord ++ tailWord_113445).sum := by decide
  have hdescent : baseEnd_113445 < baseStart_113445 := by decide
  rcases family_descends (prefixWord ++ tailWord_113445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113452 : List Nat := [2, 2, 1, 1, 1, 4, 9]
def baseStart_113452 : Nat := 118140960795 + 113452 * 2 ^ 59
def prefixEnd_113452 : Nat := 4983230072969 + 3 ^ 40 * 113452 * 2
def baseEnd_113452 : Nat := 5753620465579787874395

theorem tailTrace_113452 : CollatzResearch.WordTrace tailWord_113452 prefixEnd_113452 5753620465579787874395 := by
  unfold tailWord_113452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068967192495127452051305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2758622923326836602735073 2068967192495127452051305)
  ·
    refine ⟨1551725394371345589038479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2068967192495127452051305 1551725394371345589038479)
    ·
      refine ⟨2327588091557018383557719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551725394371345589038479 2327588091557018383557719)
      ·
        refine ⟨3491382137335527575336579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327588091557018383557719 3491382137335527575336579)
        ·
          refine ⟨5237073206003291363004869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491382137335527575336579 5237073206003291363004869)
          ·
            refine ⟨981951226125617130563413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5237073206003291363004869 981951226125617130563413)
            ·
              refine ⟨5753620465579787874395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 981951226125617130563413 5753620465579787874395)
              ·
                rfl

theorem cell20_113452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_113452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113452 prefixEnd_113452 := by exact prefixLift 113452
  have htrace : WordTrace (prefixWord ++ tailWord_113452) baseStart_113452 baseEnd_113452 := by
    simpa [prefixWord, tailWord_113452, baseEnd_113452] using wordTrace_append hprefix tailTrace_113452
  have hstable : (prefixWord ++ tailWord_113452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113452).length < 2 ^ (prefixWord ++ tailWord_113452).sum := by decide
  have hdescent : baseEnd_113452 < baseStart_113452 := by decide
  rcases family_descends (prefixWord ++ tailWord_113452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113507 : List Nat := [1, 1, 1, 5, 3, 3, 6]
def baseStart_113507 : Nat := 118140960795 + 113507 * 2 ^ 59
def prefixEnd_113507 : Nat := 4983230072969 + 3 ^ 40 * 113507 * 2
def baseEnd_113507 : Nat := 5756409743209149337333

theorem tailTrace_113507 : CollatzResearch.WordTrace tailWord_113507 prefixEnd_113507 5756409743209149337333 := by
  unfold tailWord_113507
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139940399790999297354775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2759960266527332864903183 4139940399790999297354775)
  ·
    refine ⟨6209910599686498946032163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4139940399790999297354775 6209910599686498946032163)
    ·
      refine ⟨9314865899529748419048245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209910599686498946032163 9314865899529748419048245)
      ·
        refine ⟨873268678080913914285773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9314865899529748419048245 873268678080913914285773)
        ·
          refine ⟨327475754280342717857165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 873268678080913914285773 327475754280342717857165)
          ·
            refine ⟨122803407855128519196437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327475754280342717857165 122803407855128519196437)
            ·
              refine ⟨5756409743209149337333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122803407855128519196437 5756409743209149337333)
              ·
                rfl

theorem cell20_113507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_113507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113507 prefixEnd_113507 := by exact prefixLift 113507
  have htrace : WordTrace (prefixWord ++ tailWord_113507) baseStart_113507 baseEnd_113507 := by
    simpa [prefixWord, tailWord_113507, baseEnd_113507] using wordTrace_append hprefix tailTrace_113507
  have hstable : (prefixWord ++ tailWord_113507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113507).length < 2 ^ (prefixWord ++ tailWord_113507).sum := by decide
  have hdescent : baseEnd_113507 < baseStart_113507 := by decide
  rcases family_descends (prefixWord ++ tailWord_113507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113531 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 3]
def baseStart_113531 : Nat := 118140960795 + 113531 * 2 ^ 59
def prefixEnd_113531 : Nat := 4983230072969 + 3 ^ 40 * 113531 * 2
def baseEnd_113531 : Nat := 51818641942844927235899

theorem tailTrace_113531 : CollatzResearch.WordTrace tailWord_113531 prefixEnd_113531 51818641942844927235899 := by
  unfold tailWord_113531
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140815751704051396228447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2760543834469367597485631 4140815751704051396228447)
  ·
    refine ⟨6211223627556077094342671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4140815751704051396228447 6211223627556077094342671)
    ·
      refine ⟨9316835441334115641514007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6211223627556077094342671 9316835441334115641514007)
      ·
        refine ⟨13975253162001173462271011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9316835441334115641514007 13975253162001173462271011)
        ·
          refine ⟨20962879743001760193406517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13975253162001173462271011 20962879743001760193406517)
          ·
            refine ⟨1965269975906415018131861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20962879743001760193406517 1965269975906415018131861)
            ·
              refine ⟨92122030120613203974931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1965269975906415018131861 92122030120613203974931)
              ·
                refine ⟨138183045180919805962397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92122030120613203974931 138183045180919805962397)
                ·
                  refine ⟨51818641942844927235899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138183045180919805962397 51818641942844927235899)
                  ·
                    rfl

theorem cell20_113531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_113531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113531 prefixEnd_113531 := by exact prefixLift 113531
  have htrace : WordTrace (prefixWord ++ tailWord_113531) baseStart_113531 baseEnd_113531 := by
    simpa [prefixWord, tailWord_113531, baseEnd_113531] using wordTrace_append hprefix tailTrace_113531
  have hstable : (prefixWord ++ tailWord_113531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113531).length < 2 ^ (prefixWord ++ tailWord_113531).sum := by decide
  have hdescent : baseEnd_113531 < baseStart_113531 := by decide
  rcases family_descends (prefixWord ++ tailWord_113531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113569 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_113569 : Nat := 118140960795 + 113569 * 2 ^ 59
def prefixEnd_113569 : Nat := 4983230072969 + 3 ^ 40 * 113569 * 2
def baseEnd_113569 : Nat := 51835986178285683969077

theorem tailTrace_113569 : CollatzResearch.WordTrace tailWord_113569 prefixEnd_113569 51835986178285683969077 := by
  unfold tailWord_113569
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142201725566383886111761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2761467817044255924074507 4142201725566383886111761)
  ·
    refine ⟨3106651294174787914583821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4142201725566383886111761 3106651294174787914583821)
    ·
      refine ⟨1164994235315545467968933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3106651294174787914583821 1164994235315545467968933)
      ·
        refine ⟨218436419121664775244175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1164994235315545467968933 218436419121664775244175)
        ·
          refine ⟨327654628682497162866263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218436419121664775244175 327654628682497162866263)
          ·
            refine ⟨491481943023745744299395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327654628682497162866263 491481943023745744299395)
            ·
              refine ⟨737222914535618616449093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491481943023745744299395 737222914535618616449093)
              ·
                refine ⟨138229296475428490584205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737222914535618616449093 138229296475428490584205)
                ·
                  refine ⟨51835986178285683969077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138229296475428490584205 51835986178285683969077)
                  ·
                    rfl

theorem cell20_113569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_113569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113569 prefixEnd_113569 := by exact prefixLift 113569
  have htrace : WordTrace (prefixWord ++ tailWord_113569) baseStart_113569 baseEnd_113569 := by
    simpa [prefixWord, tailWord_113569, baseEnd_113569] using wordTrace_append hprefix tailTrace_113569
  have hstable : (prefixWord ++ tailWord_113569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113569).length < 2 ^ (prefixWord ++ tailWord_113569).sum := by decide
  have hdescent : baseEnd_113569 < baseStart_113569 := by decide
  rcases family_descends (prefixWord ++ tailWord_113569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113621 : List Nat := [1, 3, 2, 3, 3, 1, 7]
def baseStart_113621 : Nat := 118140960795 + 113621 * 2 ^ 59
def prefixEnd_113621 : Nat := 4983230072969 + 3 ^ 40 * 113621 * 2
def baseEnd_113621 : Nat := 5762191155022734915059

theorem tailTrace_113621 : CollatzResearch.WordTrace tailWord_113621 prefixEnd_113621 5762191155022734915059 := by
  unfold tailWord_113621
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144098321377996767004717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2762732214251997844669811 4144098321377996767004717)
  ·
    refine ⟨1554036870516748787626769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4144098321377996767004717 1554036870516748787626769)
    ·
      refine ⟨1165527652887561590720077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1554036870516748787626769 1165527652887561590720077)
      ·
        refine ⟨437072869832835596520029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1165527652887561590720077 437072869832835596520029)
        ·
          refine ⟨163902326187313348695011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437072869832835596520029 163902326187313348695011)
          ·
            refine ⟨245853489280970023042517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163902326187313348695011 245853489280970023042517)
            ·
              refine ⟨5762191155022734915059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245853489280970023042517 5762191155022734915059)
              ·
                rfl

theorem cell20_113621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_113621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113621 prefixEnd_113621 := by exact prefixLift 113621
  have htrace : WordTrace (prefixWord ++ tailWord_113621) baseStart_113621 baseEnd_113621 := by
    simpa [prefixWord, tailWord_113621, baseEnd_113621] using wordTrace_append hprefix tailTrace_113621
  have hstable : (prefixWord ++ tailWord_113621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113621).length < 2 ^ (prefixWord ++ tailWord_113621).sum := by decide
  have hdescent : baseEnd_113621 < baseStart_113621 := by decide
  rcases family_descends (prefixWord ++ tailWord_113621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113682 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_113682 : Nat := 118140960795 + 113682 * 2 ^ 59
def prefixEnd_113682 : Nat := 4983230072969 + 3 ^ 40 * 113682 * 2
def baseEnd_113682 : Nat := 51887562457359513201949

theorem tailTrace_113682 : CollatzResearch.WordTrace tailWord_113682 prefixEnd_113682 51887562457359513201949 := by
  unfold tailWord_113682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036580793539251046243825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2764215449438002789983533 1036580793539251046243825)
  ·
    refine ⟨777435595154438284682869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1036580793539251046243825 777435595154438284682869)
    ·
      refine ⟨72884587045728589189019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 777435595154438284682869 72884587045728589189019)
      ·
        refine ⟨109326880568592883783529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72884587045728589189019 109326880568592883783529)
        ·
          refine ⟨81995160426444662837647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109326880568592883783529 81995160426444662837647)
          ·
            refine ⟨122992740639666994256471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81995160426444662837647 122992740639666994256471)
            ·
              refine ⟨184489110959500491384707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122992740639666994256471 184489110959500491384707)
              ·
                refine ⟨276733666439250737077061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184489110959500491384707 276733666439250737077061)
                ·
                  refine ⟨51887562457359513201949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276733666439250737077061 51887562457359513201949)
                  ·
                    rfl

theorem cell20_113682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_113682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113682 prefixEnd_113682 := by exact prefixLift 113682
  have htrace : WordTrace (prefixWord ++ tailWord_113682) baseStart_113682 baseEnd_113682 := by
    simpa [prefixWord, tailWord_113682, baseEnd_113682] using wordTrace_append hprefix tailTrace_113682
  have hstable : (prefixWord ++ tailWord_113682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113682).length < 2 ^ (prefixWord ++ tailWord_113682).sum := by decide
  have hdescent : baseEnd_113682 < baseStart_113682 := by decide
  rcases family_descends (prefixWord ++ tailWord_113682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113696 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 3]
def baseStart_113696 : Nat := 118140960795 + 113696 * 2 ^ 59
def prefixEnd_113696 : Nat := 4983230072969 + 3 ^ 40 * 113696 * 2
def baseEnd_113696 : Nat := 51893952438837686735225

theorem tailTrace_113696 : CollatzResearch.WordTrace tailWord_113696 prefixEnd_113696 51893952438837686735225 := by
  unfold tailWord_113696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073416898053142287992471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2764555864070856383989961 2073416898053142287992471)
  ·
    refine ⟨3110125347079713431988707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2073416898053142287992471 3110125347079713431988707)
    ·
      refine ⟨4665188020619570147983061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110125347079713431988707 4665188020619570147983061)
      ·
        refine ⟨109340344233271175343353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4665188020619570147983061 109340344233271175343353)
        ·
          refine ⟨82005258174953381507515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109340344233271175343353 82005258174953381507515)
          ·
            refine ⟨123007887262430072261273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82005258174953381507515 123007887262430072261273)
            ·
              refine ⟨92255915446822554195955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123007887262430072261273 92255915446822554195955)
              ·
                refine ⟨138383873170233831293933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92255915446822554195955 138383873170233831293933)
                ·
                  refine ⟨51893952438837686735225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138383873170233831293933 51893952438837686735225)
                  ·
                    rfl

theorem cell20_113696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_113696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113696 prefixEnd_113696 := by exact prefixLift 113696
  have htrace : WordTrace (prefixWord ++ tailWord_113696) baseStart_113696 baseEnd_113696 := by
    simpa [prefixWord, tailWord_113696, baseEnd_113696] using wordTrace_append hprefix tailTrace_113696
  have hstable : (prefixWord ++ tailWord_113696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113696).length < 2 ^ (prefixWord ++ tailWord_113696).sum := by decide
  have hdescent : baseEnd_113696 < baseStart_113696 := by decide
  rcases family_descends (prefixWord ++ tailWord_113696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113697 : List Nat := [1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_113697 : Nat := 118140960795 + 113697 * 2 ^ 59
def prefixEnd_113697 : Nat := 4983230072969 + 3 ^ 40 * 113697 * 2
def baseEnd_113697 : Nat := 17298136288695375900629

theorem tailTrace_113697 : CollatzResearch.WordTrace tailWord_113697 prefixEnd_113697 17298136288695375900629 := by
  unfold tailWord_113697
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146870269102661746771345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2764580179401774497847563 4146870269102661746771345)
  ·
    refine ⟨3110152701826996310078509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4146870269102661746771345 3110152701826996310078509)
    ·
      refine ⟨1166307263185123616279441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3110152701826996310078509 1166307263185123616279441)
      ·
        refine ⟨874730447388842712209581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166307263185123616279441 874730447388842712209581)
        ·
          refine ⟨328023917770816017078593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874730447388842712209581 328023917770816017078593)
          ·
            refine ⟨246017938328112012808945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328023917770816017078593 246017938328112012808945)
            ·
              refine ⟨184513453746084009606709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246017938328112012808945 184513453746084009606709)
              ·
                refine ⟨17298136288695375900629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184513453746084009606709 17298136288695375900629)
                ·
                  rfl

theorem cell20_113697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_113697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113697 prefixEnd_113697 := by exact prefixLift 113697
  have htrace : WordTrace (prefixWord ++ tailWord_113697) baseStart_113697 baseEnd_113697 := by
    simpa [prefixWord, tailWord_113697, baseEnd_113697] using wordTrace_append hprefix tailTrace_113697
  have hstable : (prefixWord ++ tailWord_113697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113697).length < 2 ^ (prefixWord ++ tailWord_113697).sum := by decide
  have hdescent : baseEnd_113697 < baseStart_113697 := by decide
  rcases family_descends (prefixWord ++ tailWord_113697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113700 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_113700 : Nat := 118140960795 + 113700 * 2 ^ 59
def prefixEnd_113700 : Nat := 4983230072969 + 3 ^ 40 * 113700 * 2
def baseEnd_113700 : Nat := 51895778147831450601875

theorem tailTrace_113700 : CollatzResearch.WordTrace tailWord_113700 prefixEnd_113700 51895778147831450601875 := by
  unfold tailWord_113700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073489844045896629565277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2764653125394528839420369 2073489844045896629565277)
  ·
    refine ⟨777558691517211236086979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2073489844045896629565277 777558691517211236086979)
    ·
      refine ⟨1166338037275816854130469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777558691517211236086979 1166338037275816854130469)
      ·
        refine ⟨218688381989215660149463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1166338037275816854130469 218688381989215660149463)
        ·
          refine ⟨328032572983823490224195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218688381989215660149463 328032572983823490224195)
          ·
            refine ⟨492048859475735235336293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328032572983823490224195 492048859475735235336293)
            ·
              refine ⟨92259161151700356625555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 492048859475735235336293 92259161151700356625555)
              ·
                refine ⟨138388741727550534938333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92259161151700356625555 138388741727550534938333)
                ·
                  refine ⟨51895778147831450601875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138388741727550534938333 51895778147831450601875)
                  ·
                    rfl

theorem cell20_113700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_113700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113700 prefixEnd_113700 := by exact prefixLift 113700
  have htrace : WordTrace (prefixWord ++ tailWord_113700) baseStart_113700 baseEnd_113700 := by
    simpa [prefixWord, tailWord_113700, baseEnd_113700] using wordTrace_append hprefix tailTrace_113700
  have hstable : (prefixWord ++ tailWord_113700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113700).length < 2 ^ (prefixWord ++ tailWord_113700).sum := by decide
  have hdescent : baseEnd_113700 < baseStart_113700 := by decide
  rcases family_descends (prefixWord ++ tailWord_113700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113728 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 2]
def baseStart_113728 : Nat := 118140960795 + 113728 * 2 ^ 59
def prefixEnd_113728 : Nat := 4983230072969 + 3 ^ 40 * 113728 * 2
def baseEnd_113728 : Nat := 51908558110787797668427

theorem tailTrace_113728 : CollatzResearch.WordTrace tailWord_113728 prefixEnd_113728 51908558110787797668427 := by
  unfold tailWord_113728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074000465995177020574919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2765333954660236027433225 2074000465995177020574919)
  ·
    refine ⟨3111000698992765530862379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074000465995177020574919 3111000698992765530862379)
    ·
      refine ⟨4666501048489148296293569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111000698992765530862379 4666501048489148296293569)
      ·
        refine ⟨3499875786366861222220177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4666501048489148296293569 3499875786366861222220177)
        ·
          refine ⟨2624906839775145916665133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3499875786366861222220177 2624906839775145916665133)
          ·
            refine ⟨984340064915679718749425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2624906839775145916665133 984340064915679718749425)
            ·
              refine ⟨738255048686759789062069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984340064915679718749425 738255048686759789062069)
              ·
                refine ⟨69211410814383730224569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 738255048686759789062069 69211410814383730224569)
                ·
                  refine ⟨51908558110787797668427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69211410814383730224569 51908558110787797668427)
                  ·
                    rfl

theorem cell20_113728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_113728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113728 prefixEnd_113728 := by exact prefixLift 113728
  have htrace : WordTrace (prefixWord ++ tailWord_113728) baseStart_113728 baseEnd_113728 := by
    simpa [prefixWord, tailWord_113728, baseEnd_113728] using wordTrace_append hprefix tailTrace_113728
  have hstable : (prefixWord ++ tailWord_113728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113728).length < 2 ^ (prefixWord ++ tailWord_113728).sum := by decide
  have hdescent : baseEnd_113728 < baseStart_113728 := by decide
  rcases family_descends (prefixWord ++ tailWord_113728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113741 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 2]
def baseStart_113741 : Nat := 118140960795 + 113741 * 2 ^ 59
def prefixEnd_113741 : Nat := 4983230072969 + 3 ^ 40 * 113741 * 2
def baseEnd_113741 : Nat := 51914491665017530235041

theorem tailTrace_113741 : CollatzResearch.WordTrace tailWord_113741 prefixEnd_113741 51914491665017530235041 := by
  unfold tailWord_113741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148475080943257261373077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2765650053962171507582051 4148475080943257261373077)
  ·
    refine ⟨194459769419215184126863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4148475080943257261373077 194459769419215184126863)
    ·
      refine ⟨291689654128822776190295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194459769419215184126863 291689654128822776190295)
      ·
        refine ⟨437534481193234164285443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291689654128822776190295 437534481193234164285443)
        ·
          refine ⟨656301721789851246428165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437534481193234164285443 656301721789851246428165)
          ·
            refine ⟨123056572835597108705281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656301721789851246428165 123056572835597108705281)
            ·
              refine ⟨92292429626697831528961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123056572835597108705281 92292429626697831528961)
              ·
                refine ⟨69219322220023373646721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92292429626697831528961 69219322220023373646721)
                ·
                  refine ⟨51914491665017530235041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69219322220023373646721 51914491665017530235041)
                  ·
                    rfl

theorem cell20_113741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_113741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113741 prefixEnd_113741 := by exact prefixLift 113741
  have htrace : WordTrace (prefixWord ++ tailWord_113741) baseStart_113741 baseEnd_113741 := by
    simpa [prefixWord, tailWord_113741, baseEnd_113741] using wordTrace_append hprefix tailTrace_113741
  have hstable : (prefixWord ++ tailWord_113741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113741).length < 2 ^ (prefixWord ++ tailWord_113741).sum := by decide
  have hdescent : baseEnd_113741 < baseStart_113741 := by decide
  rcases family_descends (prefixWord ++ tailWord_113741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113745 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 2]
def baseStart_113745 : Nat := 118140960795 + 113745 * 2 ^ 59
def prefixEnd_113745 : Nat := 4983230072969 + 3 ^ 40 * 113745 * 2
def baseEnd_113745 : Nat := 51916317374011294101691

theorem tailTrace_113745 : CollatzResearch.WordTrace tailWord_113745 prefixEnd_113745 51916317374011294101691 := by
  unfold tailWord_113745
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148620972928765944518689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2765747315285843963012459 4148620972928765944518689)
  ·
    refine ⟨3111465729696574458389017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4148620972928765944518689 3111465729696574458389017)
    ·
      refine ⟨2333599297272430843791763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3111465729696574458389017 2333599297272430843791763)
      ·
        refine ⟨3500398945908646265687645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333599297272430843791763 3500398945908646265687645)
        ·
          refine ⟨1312649604715742349632867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3500398945908646265687645 1312649604715742349632867)
          ·
            refine ⟨1968974407073613524449301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312649604715742349632867 1968974407073613524449301)
            ·
              refine ⟨92295675331575633958561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1968974407073613524449301 92295675331575633958561)
              ·
                refine ⟨69221756498681725468921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92295675331575633958561 69221756498681725468921)
                ·
                  refine ⟨51916317374011294101691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69221756498681725468921 51916317374011294101691)
                  ·
                    rfl

theorem cell20_113745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_113745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113745 prefixEnd_113745 := by exact prefixLift 113745
  have htrace : WordTrace (prefixWord ++ tailWord_113745) baseStart_113745 baseEnd_113745 := by
    simpa [prefixWord, tailWord_113745, baseEnd_113745] using wordTrace_append hprefix tailTrace_113745
  have hstable : (prefixWord ++ tailWord_113745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113745).length < 2 ^ (prefixWord ++ tailWord_113745).sum := by decide
  have hdescent : baseEnd_113745 < baseStart_113745 := by decide
  rcases family_descends (prefixWord ++ tailWord_113745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113749 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_113749 : Nat := 118140960795 + 113749 * 2 ^ 59
def prefixEnd_113749 : Nat := 4983230072969 + 3 ^ 40 * 113749 * 2
def baseEnd_113749 : Nat := 51918143083005057968341

theorem tailTrace_113749 : CollatzResearch.WordTrace tailWord_113749 prefixEnd_113749 51918143083005057968341 := by
  unfold tailWord_113749
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148766864914274627664301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2765844576609516418442867 4148766864914274627664301)
  ·
    refine ⟨1555787574342852985374113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4148766864914274627664301 1555787574342852985374113)
    ·
      refine ⟨1166840680757139739030585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1555787574342852985374113 1166840680757139739030585)
      ·
        refine ⟨875130510567854804272939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166840680757139739030585 875130510567854804272939)
        ·
          refine ⟨1312695765851782206409409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875130510567854804272939 1312695765851782206409409)
          ·
            refine ⟨984521824388836654807057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312695765851782206409409 984521824388836654807057)
            ·
              refine ⟨738391368291627491105293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984521824388836654807057 738391368291627491105293)
              ·
                refine ⟨276896763109360309164485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738391368291627491105293 276896763109360309164485)
                ·
                  refine ⟨51918143083005057968341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276896763109360309164485 51918143083005057968341)
                  ·
                    rfl

theorem cell20_113749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_113749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113749 prefixEnd_113749 := by exact prefixLift 113749
  have htrace : WordTrace (prefixWord ++ tailWord_113749) baseStart_113749 baseEnd_113749 := by
    simpa [prefixWord, tailWord_113749, baseEnd_113749] using wordTrace_append hprefix tailTrace_113749
  have hstable : (prefixWord ++ tailWord_113749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113749).length < 2 ^ (prefixWord ++ tailWord_113749).sum := by decide
  have hdescent : baseEnd_113749 < baseStart_113749 := by decide
  rcases family_descends (prefixWord ++ tailWord_113749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113763 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_113763 : Nat := 118140960795 + 113763 * 2 ^ 59
def prefixEnd_113763 : Nat := 4983230072969 + 3 ^ 40 * 113763 * 2
def baseEnd_113763 : Nat := 51924533064483231501617

theorem tailTrace_113763 : CollatzResearch.WordTrace tailWord_113763 prefixEnd_113763 51924533064483231501617 := by
  unfold tailWord_113763
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149277486863555018673943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2766184991242370012449295 4149277486863555018673943)
  ·
    refine ⟨6223916230295332528010915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149277486863555018673943 6223916230295332528010915)
    ·
      refine ⟨9335874345442998792016373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223916230295332528010915 9335874345442998792016373)
      ·
        refine ⟨875238219885281136751535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9335874345442998792016373 875238219885281136751535)
        ·
          refine ⟨1312857329827921705127303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875238219885281136751535 1312857329827921705127303)
          ·
            refine ⟨1969285994741882557690955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312857329827921705127303 1969285994741882557690955)
            ·
              refine ⟨2953928992112823836536433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969285994741882557690955 2953928992112823836536433)
              ·
                refine ⟨2215446744084617877402325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953928992112823836536433 2215446744084617877402325)
                ·
                  refine ⟨51924533064483231501617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2215446744084617877402325 51924533064483231501617)
                  ·
                    rfl

theorem cell20_113763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_113763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113763 prefixEnd_113763 := by exact prefixLift 113763
  have htrace : WordTrace (prefixWord ++ tailWord_113763) baseStart_113763 baseEnd_113763 := by
    simpa [prefixWord, tailWord_113763, baseEnd_113763] using wordTrace_append hprefix tailTrace_113763
  have hstable : (prefixWord ++ tailWord_113763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113763).length < 2 ^ (prefixWord ++ tailWord_113763).sum := by decide
  have hdescent : baseEnd_113763 < baseStart_113763 := by decide
  rcases family_descends (prefixWord ++ tailWord_113763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113825 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_113825 : Nat := 118140960795 + 113825 * 2 ^ 59
def prefixEnd_113825 : Nat := 4983230072969 + 3 ^ 40 * 113825 * 2
def baseEnd_113825 : Nat := 51952831553886571434697

theorem tailTrace_113825 : CollatzResearch.WordTrace tailWord_113825 prefixEnd_113825 51952831553886571434697 := by
  unfold tailWord_113825
  simp only [CollatzResearch.WordTrace]
  refine ⟨4151538812638939607430929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2767692541759293071620619 4151538812638939607430929)
  ·
    refine ⟨3113654109479204705573197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4151538812638939607430929 3113654109479204705573197)
    ·
      refine ⟨1167620291054701764589949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3113654109479204705573197 1167620291054701764589949)
      ·
        refine ⟨437857609145513161721231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1167620291054701764589949 437857609145513161721231)
        ·
          refine ⟨656786413718269742581847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437857609145513161721231 656786413718269742581847)
          ·
            refine ⟨985179620577404613872771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656786413718269742581847 985179620577404613872771)
            ·
              refine ⟨1477769430866106920809157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985179620577404613872771 1477769430866106920809157)
              ·
                refine ⟨277081768287395047651717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1477769430866106920809157 277081768287395047651717)
                ·
                  refine ⟨51952831553886571434697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277081768287395047651717 51952831553886571434697)
                  ·
                    rfl

theorem cell20_113825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_113825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113825 prefixEnd_113825 := by exact prefixLift 113825
  have htrace : WordTrace (prefixWord ++ tailWord_113825) baseStart_113825 baseEnd_113825 := by
    simpa [prefixWord, tailWord_113825, baseEnd_113825] using wordTrace_append hprefix tailTrace_113825
  have hstable : (prefixWord ++ tailWord_113825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113825).length < 2 ^ (prefixWord ++ tailWord_113825).sum := by decide
  have hdescent : baseEnd_113825 < baseStart_113825 := by decide
  rcases family_descends (prefixWord ++ tailWord_113825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113828 : List Nat := [2, 3, 1, 2, 3, 3, 2, 4]
def baseStart_113828 : Nat := 118140960795 + 113828 * 2 ^ 59
def prefixEnd_113828 : Nat := 4983230072969 + 3 ^ 40 * 113828 * 2
def baseEnd_113828 : Nat := 17318066945210631444895

theorem tailTrace_113828 : CollatzResearch.WordTrace tailWord_113828 prefixEnd_113828 17318066945210631444895 := by
  unfold tailWord_113828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075824115814035559895069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2767765487752047413193425 2075824115814035559895069)
  ·
    refine ⟨778434043430263334960651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2075824115814035559895069 778434043430263334960651)
    ·
      refine ⟨1167651065145395002440977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778434043430263334960651 1167651065145395002440977)
      ·
        refine ⟨875738298859046251830733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1167651065145395002440977 875738298859046251830733)
        ·
          refine ⟨328401862072142344436525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 875738298859046251830733 328401862072142344436525)
          ·
            refine ⟨123150698277053379163697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328401862072142344436525 123150698277053379163697)
            ·
              refine ⟨92363023707790034372773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123150698277053379163697 92363023707790034372773)
              ·
                refine ⟨17318066945210631444895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92363023707790034372773 17318066945210631444895)
                ·
                  rfl

theorem cell20_113828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_113828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113828 prefixEnd_113828 := by exact prefixLift 113828
  have htrace : WordTrace (prefixWord ++ tailWord_113828) baseStart_113828 baseEnd_113828 := by
    simpa [prefixWord, tailWord_113828, baseEnd_113828] using wordTrace_append hprefix tailTrace_113828
  have hstable : (prefixWord ++ tailWord_113828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113828).length < 2 ^ (prefixWord ++ tailWord_113828).sum := by decide
  have hdescent : baseEnd_113828 < baseStart_113828 := by decide
  rcases family_descends (prefixWord ++ tailWord_113828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113839 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_113839 : Nat := 118140960795 + 113839 * 2 ^ 59
def prefixEnd_113839 : Nat := 4983230072969 + 3 ^ 40 * 113839 * 2
def baseEnd_113839 : Nat := 51959221535364744967973

theorem tailTrace_113839 : CollatzResearch.WordTrace tailWord_113839 prefixEnd_113839 51959221535364744967973 := by
  unfold tailWord_113839
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152049434588219998440571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2768032956392146665627047 4152049434588219998440571)
  ·
    refine ⟨6228074151882329997660857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4152049434588219998440571 6228074151882329997660857)
    ·
      refine ⟨4671055613911747498245643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6228074151882329997660857 4671055613911747498245643)
      ·
        refine ⟨7006583420867621247368465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671055613911747498245643 7006583420867621247368465)
        ·
          refine ⟨5254937565650715935526349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7006583420867621247368465 5254937565650715935526349)
          ·
            refine ⟨1970601587119018475822381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5254937565650715935526349 1970601587119018475822381)
            ·
              refine ⟨738975595169631928433393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1970601587119018475822381 738975595169631928433393)
              ·
                refine ⟨554231696377223946325045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738975595169631928433393 554231696377223946325045)
                ·
                  refine ⟨51959221535364744967973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554231696377223946325045 51959221535364744967973)
                  ·
                    rfl

theorem cell20_113839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_113839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113839 prefixEnd_113839 := by exact prefixLift 113839
  have htrace : WordTrace (prefixWord ++ tailWord_113839) baseStart_113839 baseEnd_113839 := by
    simpa [prefixWord, tailWord_113839, baseEnd_113839] using wordTrace_append hprefix tailTrace_113839
  have hstable : (prefixWord ++ tailWord_113839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113839).length < 2 ^ (prefixWord ++ tailWord_113839).sum := by decide
  have hdescent : baseEnd_113839 < baseStart_113839 := by decide
  rcases family_descends (prefixWord ++ tailWord_113839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113862 : List Nat := [6, 1, 2, 2, 1, 1, 2, 5]
def baseStart_113862 : Nat := 118140960795 + 113862 * 2 ^ 59
def prefixEnd_113862 : Nat := 4983230072969 + 3 ^ 40 * 113862 * 2
def baseEnd_113862 : Nat := 17323239787359629067071

theorem tailTrace_113862 : CollatzResearch.WordTrace tailWord_113862 prefixEnd_113862 17323239787359629067071 := by
  unfold tailWord_113862
  simp only [CollatzResearch.WordTrace]
  refine ⟨129777759797027966453995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2768592209003263284351893 129777759797027966453995)
  ·
    refine ⟨194666639695541949680993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129777759797027966453995 194666639695541949680993)
    ·
      refine ⟨145999979771656462260745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194666639695541949680993 145999979771656462260745)
      ·
        refine ⟨109499984828742346695559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145999979771656462260745 109499984828742346695559)
        ·
          refine ⟨164249977243113520043339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109499984828742346695559 164249977243113520043339)
          ·
            refine ⟨246374965864670280065009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164249977243113520043339 246374965864670280065009)
            ·
              refine ⟨184781224398502710048757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246374965864670280065009 184781224398502710048757)
              ·
                refine ⟨17323239787359629067071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184781224398502710048757 17323239787359629067071)
                ·
                  rfl

theorem cell20_113862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_113862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113862 prefixEnd_113862 := by exact prefixLift 113862
  have htrace : WordTrace (prefixWord ++ tailWord_113862) baseStart_113862 baseEnd_113862 := by
    simpa [prefixWord, tailWord_113862, baseEnd_113862] using wordTrace_append hprefix tailTrace_113862
  have hstable : (prefixWord ++ tailWord_113862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113862).length < 2 ^ (prefixWord ++ tailWord_113862).sum := by decide
  have hdescent : baseEnd_113862 < baseStart_113862 := by decide
  rcases family_descends (prefixWord ++ tailWord_113862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113869 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 3]
def baseStart_113869 : Nat := 118140960795 + 113869 * 2 ^ 59
def prefixEnd_113869 : Nat := 4983230072969 + 3 ^ 40 * 113869 * 2
def baseEnd_113869 : Nat := 51972914352817973967851

theorem tailTrace_113869 : CollatzResearch.WordTrace tailWord_113869 prefixEnd_113869 51972914352817973967851 := by
  unfold tailWord_113869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153143624479535122032661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2768762416319690081355107 4153143624479535122032661)
  ·
    refine ⟨194678607397478208845281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4153143624479535122032661 194678607397478208845281)
    ·
      refine ⟨146008955548108656633961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194678607397478208845281 146008955548108656633961)
      ·
        refine ⟨109506716661081492475471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146008955548108656633961 109506716661081492475471)
        ·
          refine ⟨164260074991622238713207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109506716661081492475471 164260074991622238713207)
          ·
            refine ⟨246390112487433358069811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164260074991622238713207 246390112487433358069811)
            ·
              refine ⟨369585168731150037104717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246390112487433358069811 369585168731150037104717)
              ·
                refine ⟨138594438274181263914269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369585168731150037104717 138594438274181263914269)
                ·
                  refine ⟨51972914352817973967851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138594438274181263914269 51972914352817973967851)
                  ·
                    rfl

theorem cell20_113869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_113869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113869 prefixEnd_113869 := by exact prefixLift 113869
  have htrace : WordTrace (prefixWord ++ tailWord_113869) baseStart_113869 baseEnd_113869 := by
    simpa [prefixWord, tailWord_113869, baseEnd_113869] using wordTrace_append hprefix tailTrace_113869
  have hstable : (prefixWord ++ tailWord_113869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113869).length < 2 ^ (prefixWord ++ tailWord_113869).sum := by decide
  have hdescent : baseEnd_113869 < baseStart_113869 := by decide
  rcases family_descends (prefixWord ++ tailWord_113869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113932 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_113932 : Nat := 118140960795 + 113932 * 2 ^ 59
def prefixEnd_113932 : Nat := 4983230072969 + 3 ^ 40 * 113932 * 2
def baseEnd_113932 : Nat := 52001669269469754867593

theorem tailTrace_113932 : CollatzResearch.WordTrace tailWord_113932 prefixEnd_113932 52001669269469754867593 := by
  unfold tailWord_113932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077720711625648440788025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2770294282167531254384033 2077720711625648440788025)
  ·
    refine ⟨1558290533719236330591019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2077720711625648440788025 1558290533719236330591019)
    ·
      refine ⟨2337435800578854495886529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558290533719236330591019 2337435800578854495886529)
      ·
        refine ⟨1753076850434140871914897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337435800578854495886529 1753076850434140871914897)
        ·
          refine ⟨1314807637825605653936173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753076850434140871914897 1314807637825605653936173)
          ·
            refine ⟨493052864184602120226065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1314807637825605653936173 493052864184602120226065)
            ·
              refine ⟨369789648138451590169549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493052864184602120226065 369789648138451590169549)
              ·
                refine ⟨138671118051919346313581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369789648138451590169549 138671118051919346313581)
                ·
                  refine ⟨52001669269469754867593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138671118051919346313581 52001669269469754867593)
                  ·
                    rfl

theorem cell20_113932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_113932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113932 prefixEnd_113932 := by exact prefixLift 113932
  have htrace : WordTrace (prefixWord ++ tailWord_113932) baseStart_113932 baseEnd_113932 := by
    simpa [prefixWord, tailWord_113932, baseEnd_113932] using wordTrace_append hprefix tailTrace_113932
  have hstable : (prefixWord ++ tailWord_113932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113932).length < 2 ^ (prefixWord ++ tailWord_113932).sum := by decide
  have hdescent : baseEnd_113932 < baseStart_113932 := by decide
  rcases family_descends (prefixWord ++ tailWord_113932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113953 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_113953 : Nat := 118140960795 + 113953 * 2 ^ 59
def prefixEnd_113953 : Nat := 4983230072969 + 3 ^ 40 * 113953 * 2
def baseEnd_113953 : Nat := 52011254241687015167507

theorem tailTrace_113953 : CollatzResearch.WordTrace tailWord_113953 prefixEnd_113953 52011254241687015167507 := by
  unfold tailWord_113953
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156207356175217468090513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2770804904116811645393675 4156207356175217468090513)
  ·
    refine ⟨3117155517131413101067885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4156207356175217468090513 3117155517131413101067885)
    ·
      refine ⟨1168933318924279912900457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3117155517131413101067885 1168933318924279912900457)
      ·
        refine ⟨876699989193209934675343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168933318924279912900457 876699989193209934675343)
        ·
          refine ⟨1315049983789814902013015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876699989193209934675343 1315049983789814902013015)
          ·
            refine ⟨1972574975684722353019523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315049983789814902013015 1972574975684722353019523)
            ·
              refine ⟨2958862463527083529529285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972574975684722353019523 2958862463527083529529285)
              ·
                refine ⟨554786711911328161786741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2958862463527083529529285 554786711911328161786741)
                ·
                  refine ⟨52011254241687015167507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554786711911328161786741 52011254241687015167507)
                  ·
                    rfl

theorem cell20_113953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_113953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113953 prefixEnd_113953 := by exact prefixLift 113953
  have htrace : WordTrace (prefixWord ++ tailWord_113953) baseStart_113953 baseEnd_113953 := by
    simpa [prefixWord, tailWord_113953, baseEnd_113953] using wordTrace_append hprefix tailTrace_113953
  have hstable : (prefixWord ++ tailWord_113953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113953).length < 2 ^ (prefixWord ++ tailWord_113953).sum := by decide
  have hdescent : baseEnd_113953 < baseStart_113953 := by decide
  rcases family_descends (prefixWord ++ tailWord_113953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113970 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_113970 : Nat := 118140960795 + 113970 * 2 ^ 59
def prefixEnd_113970 : Nat := 4983230072969 + 3 ^ 40 * 113970 * 2
def baseEnd_113970 : Nat := 52019013504910511600771

theorem tailTrace_113970 : CollatzResearch.WordTrace tailWord_113970 prefixEnd_113970 52019013504910511600771 := by
  unfold tailWord_113970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039206849278407342864841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2771218264742419580972909 1039206849278407342864841)
  ·
    refine ⟨779405136958805507148631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1039206849278407342864841 779405136958805507148631)
    ·
      refine ⟨1169107705438208260722947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779405136958805507148631 1169107705438208260722947)
      ·
        refine ⟨1753661558157312391084421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169107705438208260722947 1753661558157312391084421)
        ·
          refine ⟨328811542154496073328329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1753661558157312391084421 328811542154496073328329)
          ·
            refine ⟨246608656615872054996247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328811542154496073328329 246608656615872054996247)
            ·
              refine ⟨369912984923808082494371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246608656615872054996247 369912984923808082494371)
              ·
                refine ⟨554869477385712123741557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369912984923808082494371 554869477385712123741557)
                ·
                  refine ⟨52019013504910511600771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554869477385712123741557 52019013504910511600771)
                  ·
                    rfl

theorem cell20_113970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_113970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_113970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_113970 prefixEnd_113970 := by exact prefixLift 113970
  have htrace : WordTrace (prefixWord ++ tailWord_113970) baseStart_113970 baseEnd_113970 := by
    simpa [prefixWord, tailWord_113970, baseEnd_113970] using wordTrace_append hprefix tailTrace_113970
  have hstable : (prefixWord ++ tailWord_113970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113970).length < 2 ^ (prefixWord ++ tailWord_113970).sum := by decide
  have hdescent : baseEnd_113970 < baseStart_113970 := by decide
  rcases family_descends (prefixWord ++ tailWord_113970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114081 : List Nat := [1, 2, 3, 14]
def baseStart_114081 : Nat := 118140960795 + 114081 * 2 ^ 59
def prefixEnd_114081 : Nat := 4983230072969 + 3 ^ 40 * 114081 * 2
def baseEnd_114081 : Nat := 214278505882664439919

theorem tailTrace_114081 : CollatzResearch.WordTrace tailWord_114081 prefixEnd_114081 214278505882664439919 := by
  unfold tailWord_114081
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160875899711495328750097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2773917266474330219166731 4160875899711495328750097)
  ·
    refine ⟨3120656924783621496562573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4160875899711495328750097 3120656924783621496562573)
    ·
      refine ⟨1170246346793858061210965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3120656924783621496562573 1170246346793858061210965)
      ·
        refine ⟨214278505882664439919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1170246346793858061210965 214278505882664439919)
        ·
          rfl

theorem cell20_114081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 14].length) (baseStart_114081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114081 prefixEnd_114081 := by exact prefixLift 114081
  have htrace : WordTrace (prefixWord ++ tailWord_114081) baseStart_114081 baseEnd_114081 := by
    simpa [prefixWord, tailWord_114081, baseEnd_114081] using wordTrace_append hprefix tailTrace_114081
  have hstable : (prefixWord ++ tailWord_114081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114081).length < 2 ^ (prefixWord ++ tailWord_114081).sum := by decide
  have hdescent : baseEnd_114081 < baseStart_114081 := by decide
  rcases family_descends (prefixWord ++ tailWord_114081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114108 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_114108 : Nat := 118140960795 + 114108 * 2 ^ 59
def prefixEnd_114108 : Nat := 4983230072969 + 3 ^ 40 * 114108 * 2
def baseEnd_114108 : Nat := 52082000465195365000207

theorem tailTrace_114108 : CollatzResearch.WordTrace tailWord_114108 prefixEnd_114108 52082000465195365000207 := by
  unfold tailWord_114108
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080930335306839469991489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2774573780409119293321985 2080930335306839469991489)
  ·
    refine ⟨1560697751480129602493617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2080930335306839469991489 1560697751480129602493617)
    ·
      refine ⟨1170523313610097201870213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1560697751480129602493617 1170523313610097201870213)
      ·
        refine ⟨219473121301893225350665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1170523313610097201870213 219473121301893225350665)
        ·
          refine ⟨164604840976419919012999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219473121301893225350665 164604840976419919012999)
          ·
            refine ⟨246907261464629878519499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164604840976419919012999 246907261464629878519499)
            ·
              refine ⟨370360892196944817779249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246907261464629878519499 370360892196944817779249)
              ·
                refine ⟨277770669147708613334437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370360892196944817779249 277770669147708613334437)
                ·
                  refine ⟨52082000465195365000207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277770669147708613334437 52082000465195365000207)
                  ·
                    rfl

theorem cell20_114108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_114108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114108 prefixEnd_114108 := by exact prefixLift 114108
  have htrace : WordTrace (prefixWord ++ tailWord_114108) baseStart_114108 baseEnd_114108 := by
    simpa [prefixWord, tailWord_114108, baseEnd_114108] using wordTrace_append hprefix tailTrace_114108
  have hstable : (prefixWord ++ tailWord_114108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114108).length < 2 ^ (prefixWord ++ tailWord_114108).sum := by decide
  have hdescent : baseEnd_114108 < baseStart_114108 := by decide
  rcases family_descends (prefixWord ++ tailWord_114108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114112 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_114112 : Nat := 118140960795 + 114112 * 2 ^ 59
def prefixEnd_114112 : Nat := 4983230072969 + 3 ^ 40 * 114112 * 2
def baseEnd_114112 : Nat := 52083826174189128866857

theorem tailTrace_114112 : CollatzResearch.WordTrace tailWord_114112 prefixEnd_114112 52083826174189128866857 := by
  unfold tailWord_114112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081003281299593811564295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2774671041732791748752393 2081003281299593811564295)
  ·
    refine ⟨3121504921949390717346443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081003281299593811564295 3121504921949390717346443)
    ·
      refine ⟨4682257382924086076019665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121504921949390717346443 4682257382924086076019665)
      ·
        refine ⟨3511693037193064557014749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4682257382924086076019665 3511693037193064557014749)
        ·
          refine ⟨1316884888947399208880531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3511693037193064557014749 1316884888947399208880531)
          ·
            refine ⟨1975327333421098813320797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316884888947399208880531 1975327333421098813320797)
            ·
              refine ⟨740747750032912054995299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1975327333421098813320797 740747750032912054995299)
              ·
                refine ⟨1111121625049368082492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740747750032912054995299 1111121625049368082492949)
                ·
                  refine ⟨52083826174189128866857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1111121625049368082492949 52083826174189128866857)
                  ·
                    rfl

theorem cell20_114112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_114112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114112 prefixEnd_114112 := by exact prefixLift 114112
  have htrace : WordTrace (prefixWord ++ tailWord_114112) baseStart_114112 baseEnd_114112 := by
    simpa [prefixWord, tailWord_114112, baseEnd_114112] using wordTrace_append hprefix tailTrace_114112
  have hstable : (prefixWord ++ tailWord_114112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114112).length < 2 ^ (prefixWord ++ tailWord_114112).sum := by decide
  have hdescent : baseEnd_114112 < baseStart_114112 := by decide
  rcases family_descends (prefixWord ++ tailWord_114112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114143 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_114143 : Nat := 118140960795 + 114143 * 2 ^ 59
def prefixEnd_114143 : Nat := 4983230072969 + 3 ^ 40 * 114143 * 2
def baseEnd_114143 : Nat := 52097975418890798833397

theorem tailTrace_114143 : CollatzResearch.WordTrace tailWord_114143 prefixEnd_114143 52097975418890798833397 := by
  unfold tailWord_114143
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163137225486879917507083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2775424816991253278338055 4163137225486879917507083)
  ·
    refine ⟨6244705838230319876260625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4163137225486879917507083 6244705838230319876260625)
    ·
      refine ⟨4683529378672739907195469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6244705838230319876260625 4683529378672739907195469)
      ·
        refine ⟨1756323517002277465198301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4683529378672739907195469 1756323517002277465198301)
        ·
          refine ⟨658621318875854049449363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1756323517002277465198301 658621318875854049449363)
          ·
            refine ⟨987931978313781074174045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658621318875854049449363 987931978313781074174045)
            ·
              refine ⟨370474491867667902815267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987931978313781074174045 370474491867667902815267)
              ·
                refine ⟨555711737801501854222901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370474491867667902815267 555711737801501854222901)
                ·
                  refine ⟨52097975418890798833397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 555711737801501854222901 52097975418890798833397)
                  ·
                    rfl

theorem cell20_114143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_114143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114143 prefixEnd_114143 := by exact prefixLift 114143
  have htrace : WordTrace (prefixWord ++ tailWord_114143) baseStart_114143 baseEnd_114143 := by
    simpa [prefixWord, tailWord_114143, baseEnd_114143] using wordTrace_append hprefix tailTrace_114143
  have hstable : (prefixWord ++ tailWord_114143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114143).length < 2 ^ (prefixWord ++ tailWord_114143).sum := by decide
  have hdescent : baseEnd_114143 < baseStart_114143 := by decide
  rcases family_descends (prefixWord ++ tailWord_114143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114180 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 2]
def baseStart_114180 : Nat := 118140960795 + 114180 * 2 ^ 59
def prefixEnd_114180 : Nat := 4983230072969 + 3 ^ 40 * 114180 * 2
def baseEnd_114180 : Nat := 52114863227083114599913

theorem tailTrace_114180 : CollatzResearch.WordTrace tailWord_114180 prefixEnd_114180 52114863227083114599913 := by
  unfold tailWord_114180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082243363176417618301997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2776324484235223491069329 2082243363176417618301997)
  ·
    refine ⟨780841261191156606863249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2082243363176417618301997 780841261191156606863249)
    ·
      refine ⟨585630945893367455147437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 780841261191156606863249 585630945893367455147437)
      ·
        refine ⟨219611604710012795680289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585630945893367455147437 219611604710012795680289)
        ·
          refine ⟨164708703532509596760217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219611604710012795680289 164708703532509596760217)
          ·
            refine ⟨123531527649382197570163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164708703532509596760217 123531527649382197570163)
            ·
              refine ⟨185297291474073296355245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123531527649382197570163 185297291474073296355245)
              ·
                refine ⟨69486484302777486133217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185297291474073296355245 69486484302777486133217)
                ·
                  refine ⟨52114863227083114599913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69486484302777486133217 52114863227083114599913)
                  ·
                    rfl

theorem cell20_114180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_114180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114180 prefixEnd_114180 := by exact prefixLift 114180
  have htrace : WordTrace (prefixWord ++ tailWord_114180) baseStart_114180 baseEnd_114180 := by
    simpa [prefixWord, tailWord_114180, baseEnd_114180] using wordTrace_append hprefix tailTrace_114180
  have hstable : (prefixWord ++ tailWord_114180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114180).length < 2 ^ (prefixWord ++ tailWord_114180).sum := by decide
  have hdescent : baseEnd_114180 < baseStart_114180 := by decide
  rcases family_descends (prefixWord ++ tailWord_114180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114184 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 2]
def baseStart_114184 : Nat := 118140960795 + 114184 * 2 ^ 59
def prefixEnd_114184 : Nat := 4983230072969 + 3 ^ 40 * 114184 * 2
def baseEnd_114184 : Nat := 52116688936076878466563

theorem tailTrace_114184 : CollatzResearch.WordTrace tailWord_114184 prefixEnd_114184 52116688936076878466563 := by
  unfold tailWord_114184
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082316309169171959874803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2776421745558895946499737 2082316309169171959874803)
  ·
    refine ⟨3123474463753757939812205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082316309169171959874803 3123474463753757939812205)
    ·
      refine ⟨1171302923907659227429577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3123474463753757939812205 1171302923907659227429577)
      ·
        refine ⟨878477192930744420572183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171302923907659227429577 878477192930744420572183)
        ·
          refine ⟨1317715789396116630858275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878477192930744420572183 1317715789396116630858275)
          ·
            refine ⟨1976573684094174946287413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317715789396116630858275 1976573684094174946287413)
            ·
              refine ⟨185303782883828901214445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1976573684094174946287413 185303782883828901214445)
              ·
                refine ⟨69488918581435837955417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185303782883828901214445 69488918581435837955417)
                ·
                  refine ⟨52116688936076878466563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69488918581435837955417 52116688936076878466563)
                  ·
                    rfl

theorem cell20_114184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_114184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114184 prefixEnd_114184 := by exact prefixLift 114184
  have htrace : WordTrace (prefixWord ++ tailWord_114184) baseStart_114184 baseEnd_114184 := by
    simpa [prefixWord, tailWord_114184, baseEnd_114184] using wordTrace_append hprefix tailTrace_114184
  have hstable : (prefixWord ++ tailWord_114184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114184).length < 2 ^ (prefixWord ++ tailWord_114184).sum := by decide
  have hdescent : baseEnd_114184 < baseStart_114184 := by decide
  rcases family_descends (prefixWord ++ tailWord_114184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114195 : List Nat := [1, 1, 1, 2, 1, 6, 8]
def baseStart_114195 : Nat := 118140960795 + 114195 * 2 ^ 59
def prefixEnd_114195 : Nat := 4983230072969 + 3 ^ 40 * 114195 * 2
def baseEnd_114195 : Nat := 5791301070645525455539

theorem tailTrace_114195 : CollatzResearch.WordTrace tailWord_114195 prefixEnd_114195 5791301070645525455539 := by
  unfold tailWord_114195
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165033821298492798400039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2776689214198995198933359 4165033821298492798400039)
  ·
    refine ⟨6247550731947739197600059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4165033821298492798400039 6247550731947739197600059)
    ·
      refine ⟨9371326097921608796400089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247550731947739197600059 9371326097921608796400089)
      ·
        refine ⟨7028494573441206597300067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9371326097921608796400089 7028494573441206597300067)
        ·
          refine ⟨10542741860161809895950101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028494573441206597300067 10542741860161809895950101)
          ·
            refine ⟨494191024695084838872661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10542741860161809895950101 494191024695084838872661)
            ·
              refine ⟨5791301070645525455539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 494191024695084838872661 5791301070645525455539)
              ·
                rfl

theorem cell20_114195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_114195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114195 prefixEnd_114195 := by exact prefixLift 114195
  have htrace : WordTrace (prefixWord ++ tailWord_114195) baseStart_114195 baseEnd_114195 := by
    simpa [prefixWord, tailWord_114195, baseEnd_114195] using wordTrace_append hprefix tailTrace_114195
  have hstable : (prefixWord ++ tailWord_114195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114195).length < 2 ^ (prefixWord ++ tailWord_114195).sum := by decide
  have hdescent : baseEnd_114195 < baseStart_114195 := by decide
  rcases family_descends (prefixWord ++ tailWord_114195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114226 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_114226 : Nat := 118140960795 + 114226 * 2 ^ 59
def prefixEnd_114226 : Nat := 4983230072969 + 3 ^ 40 * 114226 * 2
def baseEnd_114226 : Nat := 52135858880511399066391

theorem tailTrace_114226 : CollatzResearch.WordTrace tailWord_114226 prefixEnd_114226 52135858880511399066391 := by
  unfold tailWord_114226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041541121046546273194633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2777442989457456728519021 1041541121046546273194633)
  ·
    refine ⟨781155840784909704895975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1041541121046546273194633 781155840784909704895975)
    ·
      refine ⟨1171733761177364557343963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781155840784909704895975 1171733761177364557343963)
      ·
        refine ⟨1757600641766046836015945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171733761177364557343963 1757600641766046836015945)
        ·
          refine ⟨1318200481324535127011959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1757600641766046836015945 1318200481324535127011959)
          ·
            refine ⟨1977300721986802690517939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318200481324535127011959 1977300721986802690517939)
            ·
              refine ⟨2965951082980204035776909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977300721986802690517939 2965951082980204035776909)
              ·
                refine ⟨1112231656117576513416341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2965951082980204035776909 1112231656117576513416341)
                ·
                  refine ⟨52135858880511399066391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1112231656117576513416341 52135858880511399066391)
                  ·
                    rfl

theorem cell20_114226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_114226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114226 prefixEnd_114226 := by exact prefixLift 114226
  have htrace : WordTrace (prefixWord ++ tailWord_114226) baseStart_114226 baseEnd_114226 := by
    simpa [prefixWord, tailWord_114226, baseEnd_114226] using wordTrace_append hprefix tailTrace_114226
  have hstable : (prefixWord ++ tailWord_114226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114226).length < 2 ^ (prefixWord ++ tailWord_114226).sum := by decide
  have hdescent : baseEnd_114226 < baseStart_114226 := by decide
  rcases family_descends (prefixWord ++ tailWord_114226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114246 : List Nat := [6, 1, 1, 1, 4, 7]
def baseStart_114246 : Nat := 118140960795 + 114246 * 2 ^ 59
def prefixEnd_114246 : Nat := 4983230072969 + 3 ^ 40 * 114246 * 2
def baseEnd_114246 : Nat := 1931295830573341422209

theorem tailTrace_114246 : CollatzResearch.WordTrace tailWord_114246 prefixEnd_114246 1931295830573341422209 := by
  unfold tailWord_114246
  simp only [CollatzResearch.WordTrace]
  refine ⟨130215435753554015890831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2777929296075819005671061 130215435753554015890831)
  ·
    refine ⟨195323153630331023836247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130215435753554015890831 195323153630331023836247)
    ·
      refine ⟨292984730445496535754371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195323153630331023836247 292984730445496535754371)
      ·
        refine ⟨439477095668244803631557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292984730445496535754371 439477095668244803631557)
        ·
          refine ⟨82401955437795900680917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439477095668244803631557 82401955437795900680917)
          ·
            refine ⟨1931295830573341422209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82401955437795900680917 1931295830573341422209)
            ·
              rfl

theorem cell20_114246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 7].length) (baseStart_114246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114246 prefixEnd_114246 := by exact prefixLift 114246
  have htrace : WordTrace (prefixWord ++ tailWord_114246) baseStart_114246 baseEnd_114246 := by
    simpa [prefixWord, tailWord_114246, baseEnd_114246] using wordTrace_append hprefix tailTrace_114246
  have hstable : (prefixWord ++ tailWord_114246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114246).length < 2 ^ (prefixWord ++ tailWord_114246).sum := by decide
  have hdescent : baseEnd_114246 < baseStart_114246 := by decide
  rcases family_descends (prefixWord ++ tailWord_114246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114260 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 2]
def baseStart_114260 : Nat := 118140960795 + 114260 * 2 ^ 59
def prefixEnd_114260 : Nat := 4983230072969 + 3 ^ 40 * 114260 * 2
def baseEnd_114260 : Nat := 52151377406958391932919

theorem tailTrace_114260 : CollatzResearch.WordTrace tailWord_114260 prefixEnd_114260 52151377406958391932919 := by
  unfold tailWord_114260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083702283031504449758117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2778269710708672599677489 2083702283031504449758117)
  ·
    refine ⟨390694178068407084329647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2083702283031504449758117 390694178068407084329647)
    ·
      refine ⟨586041267102610626494471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390694178068407084329647 586041267102610626494471)
      ·
        refine ⟨879061900653915939741707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586041267102610626494471 879061900653915939741707)
        ·
          refine ⟨1318592850980873909612561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879061900653915939741707 1318592850980873909612561)
          ·
            refine ⟨988944638235655432209421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318592850980873909612561 988944638235655432209421)
            ·
              refine ⟨370854239338370787078533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 988944638235655432209421 370854239338370787078533)
              ·
                refine ⟨69535169875944522577225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370854239338370787078533 69535169875944522577225)
                ·
                  refine ⟨52151377406958391932919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69535169875944522577225 52151377406958391932919)
                  ·
                    rfl

theorem cell20_114260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_114260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114260 prefixEnd_114260 := by exact prefixLift 114260
  have htrace : WordTrace (prefixWord ++ tailWord_114260) baseStart_114260 baseEnd_114260 := by
    simpa [prefixWord, tailWord_114260, baseEnd_114260] using wordTrace_append hprefix tailTrace_114260
  have hstable : (prefixWord ++ tailWord_114260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114260).length < 2 ^ (prefixWord ++ tailWord_114260).sum := by decide
  have hdescent : baseEnd_114260 < baseStart_114260 := by decide
  rcases family_descends (prefixWord ++ tailWord_114260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114264 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_114264 : Nat := 118140960795 + 114264 * 2 ^ 59
def prefixEnd_114264 : Nat := 4983230072969 + 3 ^ 40 * 114264 * 2
def baseEnd_114264 : Nat := 52153203115952155799569

theorem tailTrace_114264 : CollatzResearch.WordTrace tailWord_114264 prefixEnd_114264 52153203115952155799569 := by
  unfold tailWord_114264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083775229024258791330923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2778366972032345055107897 2083775229024258791330923)
  ·
    refine ⟨3125662843536388186996385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2083775229024258791330923 3125662843536388186996385)
    ·
      refine ⟨2344247132652291140247289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3125662843536388186996385 2344247132652291140247289)
      ·
        refine ⟨1758185349489218355185467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2344247132652291140247289 1758185349489218355185467)
        ·
          refine ⟨2637278024233827532778201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758185349489218355185467 2637278024233827532778201)
          ·
            refine ⟨1977958518175370649583651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2637278024233827532778201 1977958518175370649583651)
            ·
              refine ⟨2966937777263055974375477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977958518175370649583651 2966937777263055974375477)
              ·
                refine ⟨278150416618411497597701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2966937777263055974375477 278150416618411497597701)
                ·
                  refine ⟨52153203115952155799569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278150416618411497597701 52153203115952155799569)
                  ·
                    rfl

theorem cell20_114264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_114264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114264 prefixEnd_114264 := by exact prefixLift 114264
  have htrace : WordTrace (prefixWord ++ tailWord_114264) baseStart_114264 baseEnd_114264 := by
    simpa [prefixWord, tailWord_114264, baseEnd_114264] using wordTrace_append hprefix tailTrace_114264
  have hstable : (prefixWord ++ tailWord_114264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114264).length < 2 ^ (prefixWord ++ tailWord_114264).sum := by decide
  have hdescent : baseEnd_114264 < baseStart_114264 := by decide
  rcases family_descends (prefixWord ++ tailWord_114264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114308 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 3]
def baseStart_114308 : Nat := 118140960795 + 114308 * 2 ^ 59
def prefixEnd_114308 : Nat := 4983230072969 + 3 ^ 40 * 114308 * 2
def baseEnd_114308 : Nat := 52173285914883558332723

theorem tailTrace_114308 : CollatzResearch.WordTrace tailWord_114308 prefixEnd_114308 52173285914883558332723 := by
  unfold tailWord_114308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084577634944556548631789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2779436846592742064842385 2084577634944556548631789)
  ·
    refine ⟨781716613104208705736921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2084577634944556548631789 781716613104208705736921)
    ·
      refine ⟨586287459828156529302691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781716613104208705736921 586287459828156529302691)
      ·
        refine ⟨879431189742234793954037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586287459828156529302691 879431189742234793954037)
        ·
          refine ⟨82446674038334511933191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 879431189742234793954037 82446674038334511933191)
          ·
            refine ⟨123670011057501767899787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82446674038334511933191 123670011057501767899787)
            ·
              refine ⟨185505016586252651849681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123670011057501767899787 185505016586252651849681)
              ·
                refine ⟨139128762439689488887261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185505016586252651849681 139128762439689488887261)
                ·
                  refine ⟨52173285914883558332723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139128762439689488887261 52173285914883558332723)
                  ·
                    rfl

theorem cell20_114308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_114308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114308 prefixEnd_114308 := by exact prefixLift 114308
  have htrace : WordTrace (prefixWord ++ tailWord_114308) baseStart_114308 baseEnd_114308 := by
    simpa [prefixWord, tailWord_114308, baseEnd_114308] using wordTrace_append hprefix tailTrace_114308
  have hstable : (prefixWord ++ tailWord_114308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114308).length < 2 ^ (prefixWord ++ tailWord_114308).sum := by decide
  have hdescent : baseEnd_114308 < baseStart_114308 := by decide
  rcases family_descends (prefixWord ++ tailWord_114308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114309 : List Nat := [1, 3, 1, 1, 4, 1, 9]
def baseStart_114309 : Nat := 118140960795 + 114309 * 2 ^ 59
def prefixEnd_114309 : Nat := 4983230072969 + 3 ^ 40 * 114309 * 2
def baseEnd_114309 : Nat := 5797082482459111033265

theorem tailTrace_114309 : CollatzResearch.WordTrace tailWord_114309 prefixEnd_114309 5797082482459111033265 := by
  unfold tailWord_114309
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169191742885490268049981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2779461161923660178699987 4169191742885490268049981)
  ·
    refine ⟨1563446903582058850518743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4169191742885490268049981 1563446903582058850518743)
    ·
      refine ⟨2345170355373088275778115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563446903582058850518743 2345170355373088275778115)
      ·
        refine ⟨3517755533059632413667173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345170355373088275778115 3517755533059632413667173)
        ·
          refine ⟨659579162448681077562595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3517755533059632413667173 659579162448681077562595)
          ·
            refine ⟨989368743673021616343893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659579162448681077562595 989368743673021616343893)
            ·
              refine ⟨5797082482459111033265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 989368743673021616343893 5797082482459111033265)
              ·
                rfl

theorem cell20_114309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_114309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114309 prefixEnd_114309 := by exact prefixLift 114309
  have htrace : WordTrace (prefixWord ++ tailWord_114309) baseStart_114309 baseEnd_114309 := by
    simpa [prefixWord, tailWord_114309, baseEnd_114309] using wordTrace_append hprefix tailTrace_114309
  have hstable : (prefixWord ++ tailWord_114309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114309).length < 2 ^ (prefixWord ++ tailWord_114309).sum := by decide
  have hdescent : baseEnd_114309 < baseStart_114309 := by decide
  rcases family_descends (prefixWord ++ tailWord_114309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114364 : List Nat := [2, 2, 2, 3, 1, 4, 6]
def baseStart_114364 : Nat := 118140960795 + 114364 * 2 ^ 59
def prefixEnd_114364 : Nat := 4983230072969 + 3 ^ 40 * 114364 * 2
def baseEnd_114364 : Nat := 5799871760088472496203

theorem tailTrace_114364 : CollatzResearch.WordTrace tailWord_114364 prefixEnd_114364 5799871760088472496203 := by
  unfold tailWord_114364
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085598878843117330651073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2780798505124156440868097 2085598878843117330651073)
  ·
    refine ⟨1564199159132337997988305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2085598878843117330651073 1564199159132337997988305)
    ·
      refine ⟨1173149369349253498491229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1564199159132337997988305 1173149369349253498491229)
      ·
        refine ⟨439931013505970061934211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1173149369349253498491229 439931013505970061934211)
        ·
          refine ⟨659896520258955092901317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439931013505970061934211 659896520258955092901317)
          ·
            refine ⟨123730597548554079918997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 659896520258955092901317 123730597548554079918997)
            ·
              refine ⟨5799871760088472496203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123730597548554079918997 5799871760088472496203)
              ·
                rfl

theorem cell20_114364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 6].length) (baseStart_114364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114364 prefixEnd_114364 := by exact prefixLift 114364
  have htrace : WordTrace (prefixWord ++ tailWord_114364) baseStart_114364 baseEnd_114364 := by
    simpa [prefixWord, tailWord_114364, baseEnd_114364] using wordTrace_append hprefix tailTrace_114364
  have hstable : (prefixWord ++ tailWord_114364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114364).length < 2 ^ (prefixWord ++ tailWord_114364).sum := by decide
  have hdescent : baseEnd_114364 < baseStart_114364 := by decide
  rcases family_descends (prefixWord ++ tailWord_114364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114381 : List Nat := [1, 6, 2, 1, 1, 1, 1, 7]
def baseStart_114381 : Nat := 118140960795 + 114381 * 2 ^ 59
def prefixEnd_114381 : Nat := 4983230072969 + 3 ^ 40 * 114381 * 2
def baseEnd_114381 : Nat := 17402201701339916299697

theorem tailTrace_114381 : CollatzResearch.WordTrace tailWord_114381 prefixEnd_114381 17402201701339916299697 := by
  unfold tailWord_114381
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171817798624646564670997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2781211865749764376447331 4171817798624646564670997)
  ·
    refine ⟨195553959310530307718953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4171817798624646564670997 195553959310530307718953)
    ·
      refine ⟨146665469482897730789215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195553959310530307718953 146665469482897730789215)
      ·
        refine ⟨219998204224346596183823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146665469482897730789215 219998204224346596183823)
        ·
          refine ⟨329997306336519894275735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219998204224346596183823 329997306336519894275735)
          ·
            refine ⟨494995959504779841413603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329997306336519894275735 494995959504779841413603)
            ·
              refine ⟨742493939257169762120405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494995959504779841413603 742493939257169762120405)
              ·
                refine ⟨17402201701339916299697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 742493939257169762120405 17402201701339916299697)
                ·
                  rfl

theorem cell20_114381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_114381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114381 prefixEnd_114381 := by exact prefixLift 114381
  have htrace : WordTrace (prefixWord ++ tailWord_114381) baseStart_114381 baseEnd_114381 := by
    simpa [prefixWord, tailWord_114381, baseEnd_114381] using wordTrace_append hprefix tailTrace_114381
  have hstable : (prefixWord ++ tailWord_114381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114381).length < 2 ^ (prefixWord ++ tailWord_114381).sum := by decide
  have hdescent : baseEnd_114381 < baseStart_114381 := by decide
  rcases family_descends (prefixWord ++ tailWord_114381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114385 : List Nat := [1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_114385 : Nat := 118140960795 + 114385 * 2 ^ 59
def prefixEnd_114385 : Nat := 4983230072969 + 3 ^ 40 * 114385 * 2
def baseEnd_114385 : Nat := 17402810271004504255247

theorem tailTrace_114385 : CollatzResearch.WordTrace tailWord_114385 prefixEnd_114385 17402810271004504255247 := by
  unfold tailWord_114385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171963690610155247816609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2781309127073436831877739 4171963690610155247816609)
  ·
    refine ⟨3128972767957616435862457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4171963690610155247816609 3128972767957616435862457)
    ·
      refine ⟨2346729575968212326896843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3128972767957616435862457 2346729575968212326896843)
      ·
        refine ⟨3520094363952318490345265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346729575968212326896843 3520094363952318490345265)
        ·
          refine ⟨2640070772964238867758949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520094363952318490345265 2640070772964238867758949)
          ·
            refine ⟨495013269930794787704803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2640070772964238867758949 495013269930794787704803)
            ·
              refine ⟨742519904896192181557205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495013269930794787704803 742519904896192181557205)
              ·
                refine ⟨17402810271004504255247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 742519904896192181557205 17402810271004504255247)
                ·
                  rfl

theorem cell20_114385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_114385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114385 prefixEnd_114385 := by exact prefixLift 114385
  have htrace : WordTrace (prefixWord ++ tailWord_114385) baseStart_114385 baseEnd_114385 := by
    simpa [prefixWord, tailWord_114385, baseEnd_114385] using wordTrace_append hprefix tailTrace_114385
  have hstable : (prefixWord ++ tailWord_114385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114385).length < 2 ^ (prefixWord ++ tailWord_114385).sum := by decide
  have hdescent : baseEnd_114385 < baseStart_114385 := by decide
  rcases family_descends (prefixWord ++ tailWord_114385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114450 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_114450 : Nat := 118140960795 + 114450 * 2 ^ 59
def prefixEnd_114450 : Nat := 4983230072969 + 3 ^ 40 * 114450 * 2
def baseEnd_114450 : Nat := 52238098584162175598809

theorem tailTrace_114450 : CollatzResearch.WordTrace tailWord_114450 prefixEnd_114450 52238098584162175598809 := by
  unfold tailWord_114450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043583608843667837233201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2782889623583114232621869 1043583608843667837233201)
  ·
    refine ⟨782687706632750877924901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1043583608843667837233201 782687706632750877924901)
    ·
      refine ⟨146753944993640789610919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 782687706632750877924901 146753944993640789610919)
      ·
        refine ⟨220130917490461184416379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146753944993640789610919 220130917490461184416379)
        ·
          refine ⟨330196376235691776624569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220130917490461184416379 330196376235691776624569)
          ·
            refine ⟨247647282176768832468427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330196376235691776624569 247647282176768832468427)
            ·
              refine ⟨371470923265153248702641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247647282176768832468427 371470923265153248702641)
              ·
                refine ⟨278603192448864936526981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371470923265153248702641 278603192448864936526981)
                ·
                  refine ⟨52238098584162175598809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278603192448864936526981 52238098584162175598809)
                  ·
                    rfl

theorem cell20_114450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_114450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114450 prefixEnd_114450 := by exact prefixLift 114450
  have htrace : WordTrace (prefixWord ++ tailWord_114450) baseStart_114450 baseEnd_114450 := by
    simpa [prefixWord, tailWord_114450, baseEnd_114450] using wordTrace_append hprefix tailTrace_114450
  have hstable : (prefixWord ++ tailWord_114450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114450).length < 2 ^ (prefixWord ++ tailWord_114450).sum := by decide
  have hdescent : baseEnd_114450 < baseStart_114450 := by decide
  rcases family_descends (prefixWord ++ tailWord_114450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114492 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_114492 : Nat := 118140960795 + 114492 * 2 ^ 59
def prefixEnd_114492 : Nat := 4983230072969 + 3 ^ 40 * 114492 * 2
def baseEnd_114492 : Nat := 52257268528596696198637

theorem tailTrace_114492 : CollatzResearch.WordTrace tailWord_114492 prefixEnd_114492 52257268528596696198637 := by
  unfold tailWord_114492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2087933150611256260980865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2783910867481675014641153 2087933150611256260980865)
  ·
    refine ⟨1565949862958442195735649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2087933150611256260980865 1565949862958442195735649)
    ·
      refine ⟨1174462397218831646801737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1565949862958442195735649 1174462397218831646801737)
      ·
        refine ⟨880846797914123735101303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174462397218831646801737 880846797914123735101303)
        ·
          refine ⟨1321270196871185602651955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880846797914123735101303 1321270196871185602651955)
          ·
            refine ⟨1981905295306778403977933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321270196871185602651955 1981905295306778403977933)
            ·
              refine ⟨743214485740041901491725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1981905295306778403977933 743214485740041901491725)
              ·
                refine ⟨278705432152515713059397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 743214485740041901491725 278705432152515713059397)
                ·
                  refine ⟨52257268528596696198637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278705432152515713059397 52257268528596696198637)
                  ·
                    rfl

theorem cell20_114492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_114492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114492 prefixEnd_114492 := by exact prefixLift 114492
  have htrace : WordTrace (prefixWord ++ tailWord_114492) baseStart_114492 baseEnd_114492 := by
    simpa [prefixWord, tailWord_114492, baseEnd_114492] using wordTrace_append hprefix tailTrace_114492
  have hstable : (prefixWord ++ tailWord_114492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114492).length < 2 ^ (prefixWord ++ tailWord_114492).sum := by decide
  have hdescent : baseEnd_114492 < baseStart_114492 := by decide
  rcases family_descends (prefixWord ++ tailWord_114492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114516 : List Nat := [2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_114516 : Nat := 118140960795 + 114516 * 2 ^ 59
def prefixEnd_114516 : Nat := 4983230072969 + 3 ^ 40 * 114516 * 2
def baseEnd_114516 : Nat := 17422740927519759799513

theorem tailTrace_114516 : CollatzResearch.WordTrace tailWord_114516 prefixEnd_114516 17422740927519759799513 := by
  unfold tailWord_114516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088370826567782310417701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2784494435423709747223601 2088370826567782310417701)
  ·
    refine ⟨391569529981459183203319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2088370826567782310417701 391569529981459183203319)
    ·
      refine ⟨587354294972188774804979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391569529981459183203319 587354294972188774804979)
      ·
        refine ⟨881031442458283162207469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587354294972188774804979 881031442458283162207469)
        ·
          refine ⟨330386790921856185827801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 881031442458283162207469 330386790921856185827801)
          ·
            refine ⟨247790093191392139370851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330386790921856185827801 247790093191392139370851)
            ·
              refine ⟨371685139787088209056277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247790093191392139370851 371685139787088209056277)
              ·
                refine ⟨17422740927519759799513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 371685139787088209056277 17422740927519759799513)
                ·
                  rfl

theorem cell20_114516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_114516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114516 prefixEnd_114516 := by exact prefixLift 114516
  have htrace : WordTrace (prefixWord ++ tailWord_114516) baseStart_114516 baseEnd_114516 := by
    simpa [prefixWord, tailWord_114516, baseEnd_114516] using wordTrace_append hprefix tailTrace_114516
  have hstable : (prefixWord ++ tailWord_114516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114516).length < 2 ^ (prefixWord ++ tailWord_114516).sum := by decide
  have hdescent : baseEnd_114516 < baseStart_114516 := by decide
  rcases family_descends (prefixWord ++ tailWord_114516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114644 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_114644 : Nat := 118140960795 + 114644 * 2 ^ 59
def prefixEnd_114644 : Nat := 4983230072969 + 3 ^ 40 * 114644 * 2
def baseEnd_114644 : Nat := 52326645470359723131349

theorem tailTrace_114644 : CollatzResearch.WordTrace tailWord_114644 prefixEnd_114644 52326645470359723131349 := by
  unfold tailWord_114644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090705098335921240747493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2787606797781228320996657 2090705098335921240747493)
  ·
    refine ⟨392007205937985232640155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2090705098335921240747493 392007205937985232640155)
    ·
      refine ⟨588010808906977848960233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392007205937985232640155 588010808906977848960233)
      ·
        refine ⟨441008106680233386720175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588010808906977848960233 441008106680233386720175)
        ·
          refine ⟨661512160020350080080263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441008106680233386720175 661512160020350080080263)
          ·
            refine ⟨992268240030525120120395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661512160020350080080263 992268240030525120120395)
            ·
              refine ⟨1488402360045787680180593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992268240030525120120395 1488402360045787680180593)
              ·
                refine ⟨1116301770034340760135445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488402360045787680180593 1116301770034340760135445)
                ·
                  refine ⟨52326645470359723131349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1116301770034340760135445 52326645470359723131349)
                  ·
                    rfl

theorem cell20_114644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_114644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114644 prefixEnd_114644 := by exact prefixLift 114644
  have htrace : WordTrace (prefixWord ++ tailWord_114644) baseStart_114644 baseEnd_114644 := by
    simpa [prefixWord, tailWord_114644, baseEnd_114644] using wordTrace_append hprefix tailTrace_114644
  have hstable : (prefixWord ++ tailWord_114644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114644).length < 2 ^ (prefixWord ++ tailWord_114644).sum := by decide
  have hdescent : baseEnd_114644 < baseStart_114644 := by decide
  rcases family_descends (prefixWord ++ tailWord_114644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114689 : List Nat := [1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_114689 : Nat := 118140960795 + 114689 * 2 ^ 59
def prefixEnd_114689 : Nat := 4983230072969 + 3 ^ 40 * 114689 * 2
def baseEnd_114689 : Nat := 17449061565513188877055

theorem tailTrace_114689 : CollatzResearch.WordTrace tailWord_114689 prefixEnd_114689 17449061565513188877055 := by
  unfold tailWord_114689
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183051481508815166883121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2788700987672543444588747 4183051481508815166883121)
  ·
    refine ⟨3137288611131611375162341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4183051481508815166883121 3137288611131611375162341)
    ·
      refine ⟨588241614587177132842939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3137288611131611375162341 588241614587177132842939)
      ·
        refine ⟨882362421880765699264409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588241614587177132842939 882362421880765699264409)
        ·
          refine ⟨661771816410574274448307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882362421880765699264409 661771816410574274448307)
          ·
            refine ⟨992657724615861411672461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661771816410574274448307 992657724615861411672461)
            ·
              refine ⟨372246646730948029377173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992657724615861411672461 372246646730948029377173)
              ·
                refine ⟨17449061565513188877055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 372246646730948029377173 17449061565513188877055)
                ·
                  rfl

theorem cell20_114689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_114689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114689 prefixEnd_114689 := by exact prefixLift 114689
  have htrace : WordTrace (prefixWord ++ tailWord_114689) baseStart_114689 baseEnd_114689 := by
    simpa [prefixWord, tailWord_114689, baseEnd_114689] using wordTrace_append hprefix tailTrace_114689
  have hstable : (prefixWord ++ tailWord_114689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114689).length < 2 ^ (prefixWord ++ tailWord_114689).sum := by decide
  have hdescent : baseEnd_114689 < baseStart_114689 := by decide
  rcases family_descends (prefixWord ++ tailWord_114689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114696 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_114696 : Nat := 118140960795 + 114696 * 2 ^ 59
def prefixEnd_114696 : Nat := 4983230072969 + 3 ^ 40 * 114696 * 2
def baseEnd_114696 : Nat := 52350379687278653397803

theorem tailTrace_114696 : CollatzResearch.WordTrace tailWord_114696 prefixEnd_114696 52350379687278653397803 := by
  unfold tailWord_114696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091653396241727681193971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2788871194988970241591961 2091653396241727681193971)
  ·
    refine ⟨3137480094362591521790957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2091653396241727681193971 3137480094362591521790957)
    ·
      refine ⟨1176555035385971820671609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3137480094362591521790957 1176555035385971820671609)
      ·
        refine ⟨882416276539478865503707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176555035385971820671609 882416276539478865503707)
        ·
          refine ⟨1323624414809218298255561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882416276539478865503707 1323624414809218298255561)
          ·
            refine ⟨992718311106913723691671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323624414809218298255561 992718311106913723691671)
            ·
              refine ⟨1489077466660370585537507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992718311106913723691671 1489077466660370585537507)
              ·
                refine ⟨2233616199990555878306261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489077466660370585537507 2233616199990555878306261)
                ·
                  refine ⟨52350379687278653397803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2233616199990555878306261 52350379687278653397803)
                  ·
                    rfl

theorem cell20_114696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_114696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114696 prefixEnd_114696 := by exact prefixLift 114696
  have htrace : WordTrace (prefixWord ++ tailWord_114696) baseStart_114696 baseEnd_114696 := by
    simpa [prefixWord, tailWord_114696, baseEnd_114696] using wordTrace_append hprefix tailTrace_114696
  have hstable : (prefixWord ++ tailWord_114696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114696).length < 2 ^ (prefixWord ++ tailWord_114696).sum := by decide
  have hdescent : baseEnd_114696 < baseStart_114696 := by decide
  rcases family_descends (prefixWord ++ tailWord_114696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114730 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_114730 : Nat := 118140960795 + 114730 * 2 ^ 59
def prefixEnd_114730 : Nat := 4983230072969 + 3 ^ 40 * 114730 * 2
def baseEnd_114730 : Nat := 52365898213725646264331

theorem tailTrace_114730 : CollatzResearch.WordTrace tailWord_114730 prefixEnd_114730 52365898213725646264331 := by
  unfold tailWord_114730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046136718590069792281411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2789697916240186112750429 1046136718590069792281411)
  ·
    refine ⟨1569205077885104688422117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046136718590069792281411 1569205077885104688422117)
    ·
      refine ⟨294225952103457129079147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1569205077885104688422117 294225952103457129079147)
      ·
        refine ⟨441338928155185693618721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294225952103457129079147 441338928155185693618721)
        ·
          refine ⟨331004196116389270214041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441338928155185693618721 331004196116389270214041)
          ·
            refine ⟨248253147087291952660531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331004196116389270214041 248253147087291952660531)
            ·
              refine ⟨372379720630937928990797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248253147087291952660531 372379720630937928990797)
              ·
                refine ⟨139642395236601723371549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372379720630937928990797 139642395236601723371549)
                ·
                  refine ⟨52365898213725646264331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139642395236601723371549 52365898213725646264331)
                  ·
                    rfl

theorem cell20_114730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_114730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114730 prefixEnd_114730 := by exact prefixLift 114730
  have htrace : WordTrace (prefixWord ++ tailWord_114730) baseStart_114730 baseEnd_114730 := by
    simpa [prefixWord, tailWord_114730, baseEnd_114730] using wordTrace_append hprefix tailTrace_114730
  have hstable : (prefixWord ++ tailWord_114730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114730).length < 2 ^ (prefixWord ++ tailWord_114730).sum := by decide
  have hdescent : baseEnd_114730 < baseStart_114730 := by decide
  rcases family_descends (prefixWord ++ tailWord_114730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114789 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_114789 : Nat := 118140960795 + 114789 * 2 ^ 59
def prefixEnd_114789 : Nat := 4983230072969 + 3 ^ 40 * 114789 * 2
def baseEnd_114789 : Nat := 52392827421383663297423

theorem tailTrace_114789 : CollatzResearch.WordTrace tailWord_114789 prefixEnd_114789 52392827421383663297423 := by
  unfold tailWord_114789
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186698781146532245523421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2791132520764354830348947 4186698781146532245523421)
  ·
    refine ⟨1570012042929949592071283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4186698781146532245523421 1570012042929949592071283)
    ·
      refine ⟨2355018064394924388106925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570012042929949592071283 2355018064394924388106925)
      ·
        refine ⟨883131774148096645540097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2355018064394924388106925 883131774148096645540097)
        ·
          refine ⟨662348830611072484155073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883131774148096645540097 662348830611072484155073)
          ·
            refine ⟨496761622958304363116305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662348830611072484155073 496761622958304363116305)
            ·
              refine ⟨372571217218728272337229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496761622958304363116305 372571217218728272337229)
              ·
                refine ⟨139714206457023102126461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372571217218728272337229 139714206457023102126461)
                ·
                  refine ⟨52392827421383663297423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139714206457023102126461 52392827421383663297423)
                  ·
                    rfl

theorem cell20_114789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_114789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114789 prefixEnd_114789 := by exact prefixLift 114789
  have htrace : WordTrace (prefixWord ++ tailWord_114789) baseStart_114789 baseEnd_114789 := by
    simpa [prefixWord, tailWord_114789, baseEnd_114789] using wordTrace_append hprefix tailTrace_114789
  have hstable : (prefixWord ++ tailWord_114789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114789).length < 2 ^ (prefixWord ++ tailWord_114789).sum := by decide
  have hdescent : baseEnd_114789 < baseStart_114789 := by decide
  rcases family_descends (prefixWord ++ tailWord_114789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114796 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_114796 : Nat := 118140960795 + 114796 * 2 ^ 59
def prefixEnd_114796 : Nat := 4983230072969 + 3 ^ 40 * 114796 * 2
def baseEnd_114796 : Nat := 52396022412122750064061

theorem tailTrace_114796 : CollatzResearch.WordTrace tailWord_114796 prefixEnd_114796 52396022412122750064061 := by
  unfold tailWord_114796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093477046060586220514121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2791302728080781627352161 2093477046060586220514121)
  ·
    refine ⟨1570107784545439665385591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2093477046060586220514121 1570107784545439665385591)
    ·
      refine ⟨2355161676818159498078387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570107784545439665385591 2355161676818159498078387)
      ·
        refine ⟨3532742515227239247117581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355161676818159498078387 3532742515227239247117581)
        ·
          refine ⟨1324778443210214717669093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3532742515227239247117581 1324778443210214717669093)
          ·
            refine ⟨248395958101915259562955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1324778443210214717669093 248395958101915259562955)
            ·
              refine ⟨372593937152872889344433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248395958101915259562955 372593937152872889344433)
              ·
                refine ⟨279445452864654667008325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372593937152872889344433 279445452864654667008325)
                ·
                  refine ⟨52396022412122750064061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279445452864654667008325 52396022412122750064061)
                  ·
                    rfl

theorem cell20_114796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_114796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114796 prefixEnd_114796 := by exact prefixLift 114796
  have htrace : WordTrace (prefixWord ++ tailWord_114796) baseStart_114796 baseEnd_114796 := by
    simpa [prefixWord, tailWord_114796, baseEnd_114796] using wordTrace_append hprefix tailTrace_114796
  have hstable : (prefixWord ++ tailWord_114796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114796).length < 2 ^ (prefixWord ++ tailWord_114796).sum := by decide
  have hdescent : baseEnd_114796 < baseStart_114796 := by decide
  rcases family_descends (prefixWord ++ tailWord_114796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114813 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 2]
def baseStart_114813 : Nat := 118140960795 + 114813 * 2 ^ 59
def prefixEnd_114813 : Nat := 4983230072969 + 3 ^ 40 * 114813 * 2
def baseEnd_114813 : Nat := 52403781675346246497325

theorem tailTrace_114813 : CollatzResearch.WordTrace tailWord_114813 prefixEnd_114813 52403781675346246497325 := by
  unfold tailWord_114813
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187574133059584344397093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2791716088706389562931395 4187574133059584344397093)
  ·
    refine ⟨785170149948672064574455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4187574133059584344397093 785170149948672064574455)
    ·
      refine ⟨1177755224923008096861683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785170149948672064574455 1177755224923008096861683)
      ·
        refine ⟨1766632837384512145292525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177755224923008096861683 1766632837384512145292525)
        ·
          refine ⟨662487314019192054484697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1766632837384512145292525 662487314019192054484697)
          ·
            refine ⟨496865485514394040863523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662487314019192054484697 496865485514394040863523)
            ·
              refine ⟨745298228271591061295285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496865485514394040863523 745298228271591061295285)
              ·
                refine ⟨69871708900461661996433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 745298228271591061295285 69871708900461661996433)
                ·
                  refine ⟨52403781675346246497325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69871708900461661996433 52403781675346246497325)
                  ·
                    rfl

theorem cell20_114813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_114813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114813 prefixEnd_114813 := by exact prefixLift 114813
  have htrace : WordTrace (prefixWord ++ tailWord_114813) baseStart_114813 baseEnd_114813 := by
    simpa [prefixWord, tailWord_114813, baseEnd_114813] using wordTrace_append hprefix tailTrace_114813
  have hstable : (prefixWord ++ tailWord_114813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114813).length < 2 ^ (prefixWord ++ tailWord_114813).sum := by decide
  have hdescent : baseEnd_114813 < baseStart_114813 := by decide
  rcases family_descends (prefixWord ++ tailWord_114813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114844 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_114844 : Nat := 118140960795 + 114844 * 2 ^ 59
def prefixEnd_114844 : Nat := 4983230072969 + 3 ^ 40 * 114844 * 2
def baseEnd_114844 : Nat := 52417930920047916463865

theorem tailTrace_114844 : CollatzResearch.WordTrace tailWord_114844 prefixEnd_114844 52417930920047916463865 := by
  unfold tailWord_114844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094352397973638319387793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2792469863964851092517057 2094352397973638319387793)
  ·
    refine ⟨1570764298480228739540845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2094352397973638319387793 1570764298480228739540845)
    ·
      refine ⟨589036611930085777327817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1570764298480228739540845 589036611930085777327817)
      ·
        refine ⟨441777458947564332995863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589036611930085777327817 441777458947564332995863)
        ·
          refine ⟨662666188421346499493795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441777458947564332995863 662666188421346499493795)
          ·
            refine ⟨993999282632019749240693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662666188421346499493795 993999282632019749240693)
            ·
              refine ⟨93187432746751851491315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 993999282632019749240693 93187432746751851491315)
              ·
                refine ⟨139781149120127777236973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93187432746751851491315 139781149120127777236973)
                ·
                  refine ⟨52417930920047916463865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139781149120127777236973 52417930920047916463865)
                  ·
                    rfl

theorem cell20_114844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_114844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114844 prefixEnd_114844 := by exact prefixLift 114844
  have htrace : WordTrace (prefixWord ++ tailWord_114844) baseStart_114844 baseEnd_114844 := by
    simpa [prefixWord, tailWord_114844, baseEnd_114844] using wordTrace_append hprefix tailTrace_114844
  have hstable : (prefixWord ++ tailWord_114844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114844).length < 2 ^ (prefixWord ++ tailWord_114844).sum := by decide
  have hdescent : baseEnd_114844 < baseStart_114844 := by decide
  rcases family_descends (prefixWord ++ tailWord_114844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114917 : List Nat := [1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_114917 : Nat := 118140960795 + 114917 * 2 ^ 59
def prefixEnd_114917 : Nat := 4983230072969 + 3 ^ 40 * 114917 * 2
def baseEnd_114917 : Nat := 17483750036394702343411

theorem tailTrace_114917 : CollatzResearch.WordTrace tailWord_114917 prefixEnd_114917 17483750036394702343411 := by
  unfold tailWord_114917
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191367324682810106183005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2794244883121873404122003 4191367324682810106183005)
  ·
    refine ⟨1571762746756053789818627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4191367324682810106183005 1571762746756053789818627)
    ·
      refine ⟨2357644120134080684727941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571762746756053789818627 2357644120134080684727941)
      ·
        refine ⟨442058272525140128386489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2357644120134080684727941 442058272525140128386489)
        ·
          refine ⟨331543704393855096289867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442058272525140128386489 331543704393855096289867)
          ·
            refine ⟨497315556590782644434801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331543704393855096289867 497315556590782644434801)
            ·
              refine ⟨372986667443086983326101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497315556590782644434801 372986667443086983326101)
              ·
                refine ⟨17483750036394702343411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 372986667443086983326101 17483750036394702343411)
                ·
                  rfl

theorem cell20_114917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_114917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114917 prefixEnd_114917 := by exact prefixLift 114917
  have htrace : WordTrace (prefixWord ++ tailWord_114917) baseStart_114917 baseEnd_114917 := by
    simpa [prefixWord, tailWord_114917, baseEnd_114917] using wordTrace_append hprefix tailTrace_114917
  have hstable : (prefixWord ++ tailWord_114917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114917).length < 2 ^ (prefixWord ++ tailWord_114917).sum := by decide
  have hdescent : baseEnd_114917 < baseStart_114917 := by decide
  rcases family_descends (prefixWord ++ tailWord_114917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114938 : List Nat := [3, 1, 1, 1, 1, 13]
def baseStart_114938 : Nat := 118140960795 + 114938 * 2 ^ 59
def prefixEnd_114938 : Nat := 4983230072969 + 3 ^ 40 * 114938 * 2
def baseEnd_114938 : Nat := 1942993891903754345561

theorem tailTrace_114938 : CollatzResearch.WordTrace tailWord_114938 prefixEnd_114938 1942993891903754345561 := by
  unfold tailWord_114938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048033314401682673174367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2794755505071153795131645 1048033314401682673174367)
  ·
    refine ⟨1572049971602524009761551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1048033314401682673174367 1572049971602524009761551)
    ·
      refine ⟨2358074957403786014642327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572049971602524009761551 2358074957403786014642327)
      ·
        refine ⟨3537112436105679021963491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358074957403786014642327 3537112436105679021963491)
        ·
          refine ⟨5305668654158518532945237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537112436105679021963491 5305668654158518532945237)
          ·
            refine ⟨1942993891903754345561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 5305668654158518532945237 1942993891903754345561)
            ·
              rfl

theorem cell20_114938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 13].length) (baseStart_114938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114938 prefixEnd_114938 := by exact prefixLift 114938
  have htrace : WordTrace (prefixWord ++ tailWord_114938) baseStart_114938 baseEnd_114938 := by
    simpa [prefixWord, tailWord_114938, baseEnd_114938] using wordTrace_append hprefix tailTrace_114938
  have hstable : (prefixWord ++ tailWord_114938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114938).length < 2 ^ (prefixWord ++ tailWord_114938).sum := by decide
  have hdescent : baseEnd_114938 < baseStart_114938 := by decide
  rcases family_descends (prefixWord ++ tailWord_114938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114951 : List Nat := [1, 1, 4, 5, 1, 2, 1, 5]
def baseStart_114951 : Nat := 118140960795 + 114951 * 2 ^ 59
def prefixEnd_114951 : Nat := 4983230072969 + 3 ^ 40 * 114951 * 2
def baseEnd_114951 : Nat := 17488922878543699965587

theorem tailTrace_114951 : CollatzResearch.WordTrace tailWord_114951 prefixEnd_114951 17488922878543699965587 := by
  unfold tailWord_114951
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192607406559633912920707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2795071604373089275280471 4192607406559633912920707)
  ·
    refine ⟨6288911109839450869381061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192607406559633912920707 6288911109839450869381061)
    ·
      refine ⟨1179170833094897038008949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6288911109839450869381061 1179170833094897038008949)
      ·
        refine ⟨110547265602646597313339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1179170833094897038008949 110547265602646597313339)
        ·
          refine ⟨165820898403969895970009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110547265602646597313339 165820898403969895970009)
          ·
            refine ⟨124365673802977421977507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165820898403969895970009 124365673802977421977507)
            ·
              refine ⟨186548510704466132966261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124365673802977421977507 186548510704466132966261)
              ·
                refine ⟨17488922878543699965587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186548510704466132966261 17488922878543699965587)
                ·
                  rfl

theorem cell20_114951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_114951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114951 prefixEnd_114951 := by exact prefixLift 114951
  have htrace : WordTrace (prefixWord ++ tailWord_114951) baseStart_114951 baseEnd_114951 := by
    simpa [prefixWord, tailWord_114951, baseEnd_114951] using wordTrace_append hprefix tailTrace_114951
  have hstable : (prefixWord ++ tailWord_114951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114951).length < 2 ^ (prefixWord ++ tailWord_114951).sum := by decide
  have hdescent : baseEnd_114951 < baseStart_114951 := by decide
  rcases family_descends (prefixWord ++ tailWord_114951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114993 : List Nat := [1, 2, 2, 3, 4, 1, 7]
def baseStart_114993 : Nat := 118140960795 + 114993 * 2 ^ 59
def prefixEnd_114993 : Nat := 4983230072969 + 3 ^ 40 * 114993 * 2
def baseEnd_114993 : Nat := 5831770953340624499621

theorem tailTrace_114993 : CollatzResearch.WordTrace tailWord_114993 prefixEnd_114993 5831770953340624499621 := by
  unfold tailWord_114993
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194139272407475085949633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2796092848271650057299755 4194139272407475085949633)
  ·
    refine ⟨3145604454305606314462225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4194139272407475085949633 3145604454305606314462225)
    ·
      refine ⟨2359203340729204735846669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3145604454305606314462225 2359203340729204735846669)
      ·
        refine ⟨884701252773451775942501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2359203340729204735846669 884701252773451775942501)
        ·
          refine ⟨165881484895022207989219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 884701252773451775942501 165881484895022207989219)
          ·
            refine ⟨248822227342533311983829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165881484895022207989219 248822227342533311983829)
            ·
              refine ⟨5831770953340624499621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 248822227342533311983829 5831770953340624499621)
              ·
                rfl

theorem cell20_114993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_114993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114993 prefixEnd_114993 := by exact prefixLift 114993
  have htrace : WordTrace (prefixWord ++ tailWord_114993) baseStart_114993 baseEnd_114993 := by
    simpa [prefixWord, tailWord_114993, baseEnd_114993] using wordTrace_append hprefix tailTrace_114993
  have hstable : (prefixWord ++ tailWord_114993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114993).length < 2 ^ (prefixWord ++ tailWord_114993).sum := by decide
  have hdescent : baseEnd_114993 < baseStart_114993 := by decide
  rcases family_descends (prefixWord ++ tailWord_114993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114996 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_114996 : Nat := 118140960795 + 114996 * 2 ^ 59
def prefixEnd_114996 : Nat := 4983230072969 + 3 ^ 40 * 114996 * 2
def baseEnd_114996 : Nat := 52487307861810943396577

theorem tailTrace_114996 : CollatzResearch.WordTrace tailWord_114996 prefixEnd_114996 52487307861810943396577 := by
  unfold tailWord_114996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097124345698303299154421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2796165794264404398872561 2097124345698303299154421)
  ·
    refine ⟨196605407409215934295727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2097124345698303299154421 196605407409215934295727)
    ·
      refine ⟨294908111113823901443591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196605407409215934295727 294908111113823901443591)
      ·
        refine ⟨442362166670735852165387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294908111113823901443591 442362166670735852165387)
        ·
          refine ⟨663543250006103778248081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442362166670735852165387 663543250006103778248081)
          ·
            refine ⟨497657437504577833686061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663543250006103778248081 497657437504577833686061)
            ·
              refine ⟨186621539064216687632273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497657437504577833686061 186621539064216687632273)
              ·
                refine ⟨139966154298162515724205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186621539064216687632273 139966154298162515724205)
                ·
                  refine ⟨52487307861810943396577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139966154298162515724205 52487307861810943396577)
                  ·
                    rfl

theorem cell20_114996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_114996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_114996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_114996 prefixEnd_114996 := by exact prefixLift 114996
  have htrace : WordTrace (prefixWord ++ tailWord_114996) baseStart_114996 baseEnd_114996 := by
    simpa [prefixWord, tailWord_114996, baseEnd_114996] using wordTrace_append hprefix tailTrace_114996
  have hstable : (prefixWord ++ tailWord_114996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114996).length < 2 ^ (prefixWord ++ tailWord_114996).sum := by decide
  have hdescent : baseEnd_114996 < baseStart_114996 := by decide
  rcases family_descends (prefixWord ++ tailWord_114996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115058 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_115058 : Nat := 118140960795 + 115058 * 2 ^ 59
def prefixEnd_115058 : Nat := 4983230072969 + 3 ^ 40 * 115058 * 2
def baseEnd_115058 : Nat := 52515606351214283329657

theorem tailTrace_115058 : CollatzResearch.WordTrace tailWord_115058 prefixEnd_115058 52515606351214283329657 := by
  unfold tailWord_115058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049127504292997796766457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2797673344781327458043885 1049127504292997796766457)
  ·
    refine ⟨786845628219748347574843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1049127504292997796766457 786845628219748347574843)
    ·
      refine ⟨1180268442329622521362265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786845628219748347574843 1180268442329622521362265)
      ·
        refine ⟨885201331747216891021699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1180268442329622521362265 885201331747216891021699)
        ·
          refine ⟨1327801997620825336532549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885201331747216891021699 1327801997620825336532549)
          ·
            refine ⟨248962874553904750599853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1327801997620825336532549 248962874553904750599853)
            ·
              refine ⟨93361077957714281474945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248962874553904750599853 93361077957714281474945)
              ·
                refine ⟨70020808468285711106209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93361077957714281474945 70020808468285711106209)
                ·
                  refine ⟨52515606351214283329657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70020808468285711106209 52515606351214283329657)
                  ·
                    rfl

theorem cell20_115058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_115058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115058 prefixEnd_115058 := by exact prefixLift 115058
  have htrace : WordTrace (prefixWord ++ tailWord_115058) baseStart_115058 baseEnd_115058 := by
    simpa [prefixWord, tailWord_115058, baseEnd_115058] using wordTrace_append hprefix tailTrace_115058
  have hstable : (prefixWord ++ tailWord_115058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115058).length < 2 ^ (prefixWord ++ tailWord_115058).sum := by decide
  have hdescent : baseEnd_115058 < baseStart_115058 := by decide
  rcases family_descends (prefixWord ++ tailWord_115058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
